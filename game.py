#!/usr/bin/env python3
import pygame, random, sys, time
from collections import deque

CELL = 30
COLS, ROWS = 10, 20
WIDTH, HEIGHT = COLS * CELL + 200, ROWS * CELL  # side panel added
PLAY_WIDTH = COLS * CELL
FPS = 60

# Timings (ms)
BASE_FALL_MS = 800  # level 0
LEVEL_SPEEDUP = 0.85  # multiplier per level
SOFT_DROP_MS = 40
ARE_AFTER_LOCK_MS = 200  # small delay after lock (feel)
LOCK_DELAY_MS = 500

SCORES = {0: 0, 1: 100, 2: 300, 3: 500, 4: 800}
SOFT_DROP_SCORE = 1
HARD_DROP_SCORE = 2  # per row

BLACK = (10, 10, 10)
GRAY = (40, 40, 40)
WHITE = (230, 230, 230)
COLORS = [
    (0, 240, 240),  # I - cyan
    (0, 0, 240),    # J - blue
    (255, 165, 0),  # L - orange
    (240, 240, 0),  # O - yellow
    (0, 240, 0),    # S - green
    (160, 0, 240),  # T - purple
    (240, 0, 0),    # Z - red
]

# Tetromino definitions (4x4 patterns)
# Each entry: list of rotation states (2D lists)
SHAPES = {
    "I": [
        [[0,0,0,0],
         [1,1,1,1],
         [0,0,0,0],
         [0,0,0,0]],
        [[0,0,1,0],
         [0,0,1,0],
         [0,0,1,0],
         [0,0,1,0]]
    ],
    "J": [
        [[1,0,0],
         [1,1,1],
         [0,0,0]],
    ],
    "L": [
        [[0,0,1],
         [1,1,1],
         [0,0,0]],
    ],
    "O": [
        [[1,1],
         [1,1]],
    ],
    "S": [
        [[0,1,1],
         [1,1,0],
         [0,0,0]],
    ],
    "T": [
        [[0,1,0],
         [1,1,1],
         [0,0,0]],
    ],
    "Z": [
        [[1,1,0],
         [0,1,1],
         [0,0,0]],
    ],
}

# For shapes with a single base rotation, we generate rotated variants programmatically.
def rotations_from_matrix(mat):
    """Return list of 4 rotation states from base matrix."""
    rots = []
    current = [row[:] for row in mat]
    for _ in range(4):
        rots.append([row[:] for row in current])
        # rotate 90 clockwise
        current = [list(r) for r in zip(*current[::-1])]
    # remove duplicates (O and symmetric shapes)
    uniq = []
    for r in rots:
        if r not in uniq:
            uniq.append(r)
    return uniq

# Build full rotation lists
PIECES = {}
for k, v in SHAPES.items():
    # if provided >1, use them and fill rotations by rotating last state if needed
    if len(v) > 1:
        PIECES[k] = []
        for mat in v:
            PIECES[k].extend(rotations_from_matrix(mat))
        # ensure uniqueness and up to 4 states
        uniq = []
        for r in PIECES[k]:
            if r not in uniq:
                uniq.append(r)
        PIECES[k] = uniq
    else:
        PIECES[k] = rotations_from_matrix(v[0])

# Map piece keys to colors (consistent)
PIECE_KEYS = list(PIECES.keys())  # order: I, J, L, O, S, T, Z
KEY_TO_COLOR = dict(zip(PIECE_KEYS, COLORS))

# ----- Utility -----
def new_bag():
    bag = PIECE_KEYS[:]  # 7 pieces
    random.shuffle(bag)
    return deque(bag)

def rotate_shape(shape, cw=True):
    # shape is a 2D list; rotate cw or ccw
    if cw:
        return [list(row) for row in zip(*shape[::-1])]
    else:
        return [list(row) for row in zip(*shape)][::-1]

# ----- Game classes -----
class Piece:
    def __init__(self, kind):
        self.kind = kind
        self.rot_index = 0
        self.shape_list = PIECES[kind]
        self.shape = self.shape_list[self.rot_index]
        # spawn near top center
        width = len(self.shape[0])
        self.x = COLS // 2 - width // 2
        self.y = - (len(self.shape) - 1)  # allow spawns above visible area

    def rotate(self, cw=True):
        if cw:
            self.rot_index = (self.rot_index + 1) % len(self.shape_list)
        else:
            self.rot_index = (self.rot_index - 1) % len(self.shape_list)
        self.shape = self.shape_list[self.rot_index]

    def get_cells(self, x_off=0, y_off=0):
        cells = []
        for r, row in enumerate(self.shape):
            for c, v in enumerate(row):
                if v:
                    cells.append((self.x + c + x_off, self.y + r + y_off))
        return cells

    def width(self):
        return len(self.shape[0])
    def height(self):
        return len(self.shape)

class GameState:
    def __init__(self):
        self.board = [[None for _ in range(COLS)] for _ in range(ROWS)]
        self.bag = new_bag()
        self.next_queue = deque()
        for _ in range(5):
            self._fill_next()
        self.active = self._spawn_from_queue()
        self.hold = None
        self.hold_used = False

        # timing & control
        self.last_fall = pygame.time.get_ticks()
        self.fall_ms = BASE_FALL_MS
        self.paused = False
        self.game_over = False

        # scoring
        self.score = 0
        self.lines = 0
        self.level = 0

        # lock delay
        self.grounded = False
        self.lock_start = None
        self.lock_resets_left = 15

    # bag / queue helpers
    def _fill_next(self):
        if not self.bag:
            self.bag = new_bag()
        self.next_queue.append(self.bag.popleft())

    def _spawn_from_queue(self):
        if not self.next_queue:
            self._fill_next()
        kind = self.next_queue.popleft()
        self._fill_next()
        p = Piece(kind)
        return p

    # collision helpers
    def collision(self, piece, x_off=0, y_off=0):
        for (x, y) in piece.get_cells(x_off, y_off):
            if x < 0 or x >= COLS:
                return True
            if y >= ROWS:
                return True
            if y >= 0 and self.board[y][x] is not None:
                return True
        return False

    # wall-kick: try small offsets when rotating
    def try_rotate_with_kick(self, cw=True):
        # Save state
        original_rot = piece_rot = self.active.rot_index
        original_shape = self.active.shape_list
        # rotate tentatively
        self.active.rotate(cw)
        # try offsets in order
        kicks = [(0,0), (-1,0), (1,0), (-2,0), (2,0), (0,-1)]
        for dx, dy in kicks:
            if not self.collision(self.active, dx, dy):
                # apply offset
                self.active.x += dx
                self.active.y += dy
                if self.grounded:
                    self.reset_lock_timer()
                return True
        # nothing worked: revert rotation
        # rotate back
        self.active.rot_index = original_rot
        self.active.shape = self.active.shape_list[self.active.rot_index]
        return False

    def reset_lock_timer(self):
        if self.lock_resets_left > 0:
            self.lock_start = pygame.time.get_ticks()
            self.lock_resets_left -= 1

    def lock_piece(self):
        for (x, y) in self.active.get_cells():
            if y >= 0 and y < ROWS:
                self.board[y][x] = self.active.kind
        self.clear_lines_and_score()
        self.active = self._spawn_from_queue()
        self.hold_used = False
        self.grounded = False
        self.lock_start = None
        self.lock_resets_left = 15
        # check spawn collision -> game over
        if self.collision(self.active, 0, 0):
            self.game_over = True

    def clear_lines_and_score(self):
        new_board = [row for row in self.board if any(cell is None for cell in row)]
        cleared = ROWS - len(new_board)
        if cleared > 0:
            for _ in range(cleared):
                new_board.insert(0, [None]*COLS)
            self.board = new_board
            # scoring
            self.score += SCORES.get(cleared, 0) * (self.level + 1)
            self.lines += cleared
            # level up every 10 lines
            self.level = self.lines // 10
            # speed up
            self.fall_ms = max(80, int(BASE_FALL_MS * (LEVEL_SPEEDUP ** self.level)))

    def hard_drop(self):
        drop = 0
        while not self.collision(self.active, 0, 1):
            self.active.y += 1
            drop += 1
        self.score += HARD_DROP_SCORE * drop
        self.lock_piece()
        # small ARE
        time.sleep(ARE_AFTER_LOCK_MS/1000.0)

    def soft_drop(self):
        if not self.collision(self.active, 0, 1):
            self.active.y += 1
            self.score += SOFT_DROP_SCORE

    def hold_action(self):
        if self.hold_used:
            return
        self.hold_used = True
        if self.hold is None:
            self.hold = self.active.kind
            self.active = self._spawn_from_queue()
        else:
            temp = self.hold
            self.hold = self.active.kind
            self.active = Piece(temp)
        # reset lock timers and position
        self.active.x = COLS//2 - len(self.active.shape[0])//2
        self.active.y = - (len(self.active.shape)-1)
        self.grounded = False
        self.lock_start = None
        self.lock_resets_left = 15
        if self.collision(self.active):
            self.game_over = True

    def tick(self):
        """Called by main loop to advance gravity, locking, etc."""
        if self.game_over or self.paused:
            self.last_fall = pygame.time.get_ticks()
            return

        now = pygame.time.get_ticks()
        falling_interval = SOFT_DROP_MS if pygame.key.get_pressed()[pygame.K_DOWN] else self.fall_ms

        # auto move down if interval passed
        if now - self.last_fall >= falling_interval:
            if not self.collision(self.active, 0, 1):
                self.active.y += 1
                self.grounded = False
                self.lock_start = None
            else:
                # it's on ground
                if not self.grounded:
                    self.grounded = True
                    self.lock_start = now
                # check lock delay
                if self.lock_start and now - self.lock_start >= LOCK_DELAY_MS:
                    self.lock_piece()
            self.last_fall = now

# ----- Rendering helpers -----
def draw_board(screen, state):
    # background
    pygame.draw.rect(screen, GRAY, (0, 0, PLAY_WIDTH, ROWS*CELL))
    # grid & locked blocks
    for r in range(ROWS):
        for c in range(COLS):
            cell = state.board[r][c]
            x = c*CELL
            y = r*CELL
            if cell is not None:
                color = KEY_TO_COLOR[cell]
                pygame.draw.rect(screen, color, (x+1, y+1, CELL-2, CELL-2))
    # draw grid lines
    for x in range(COLS+1):
        pygame.draw.line(screen, BLACK, (x*CELL,0), (x*CELL, ROWS*CELL))
    for y in range(ROWS+1):
        pygame.draw.line(screen, BLACK, (0,y*CELL), (PLAY_WIDTH, y*CELL))

def draw_piece(screen, piece, ghost=False):
    color = KEY_TO_COLOR[piece.kind]
    if ghost:
        color = (color[0], color[1], color[2], 80)  # not used by pygame draw rect but kept for clarity
        col = tuple(int(c*0.25) for c in color[:3])
    else:
        col = color
    for (x, y) in piece.get_cells():
        if y >= 0:
            pygame.draw.rect(screen, col, (x*CELL+1, y*CELL+1, CELL-2, CELL-2))

def draw_ghost(screen, state):
    ghost = Piece(state.active.kind)
    ghost.rot_index = state.active.rot_index
    ghost.shape = state.active.shape
    ghost.x = state.active.x
    ghost.y = state.active.y
    while not state.collision(ghost, 0, 1):
        ghost.y += 1
    # draw ghost translucent (lighter color)
    color = KEY_TO_COLOR[state.active.kind]
    dim = tuple(max(30, int(c*0.35)) for c in color)
    for (x,y) in ghost.get_cells():
        if y >= 0:
            pygame.draw.rect(screen, dim, (x*CELL+1, y*CELL+1, CELL-2, CELL-2))

def draw_side_panel(screen, state, font):
    panel_x = PLAY_WIDTH + 10
    # background
    pygame.draw.rect(screen, (20,20,20), (PLAY_WIDTH,0, WIDTH-PLAY_WIDTH, HEIGHT))
    # score & stats
    lines = [
        f"Score: {state.score}",
        f"Lines: {state.lines}",
        f"Level: {state.level}",
        "",
        "Next:"
    ]
    y = 8
    for line in lines:
        surf = font.render(line, True, WHITE)
        screen.blit(surf, (panel_x, y))
        y += surf.get_height() + 6

    # draw next queue
    nx = panel_x + 8
    ny = y
    for kind in list(state.next_queue)[:5]:
        # draw small representation (2x2 cells scaled)
        shape = PIECES[kind][0]
        for r, row in enumerate(shape):
            for c, v in enumerate(row):
                if v:
                    pygame.draw.rect(screen, KEY_TO_COLOR[kind], (nx + c*10, ny + r*10, 9, 9))
        ny += (len(shape)+1)*10

    # hold
    hold_y = HEIGHT - 120
    hold_text = font.render("Hold:", True, WHITE)
    screen.blit(hold_text, (panel_x, hold_y))
    if state.hold:
        kind = state.hold
        shape = PIECES[kind][0]
        hy = hold_y + 24
        for r,row in enumerate(shape):
            for c,v in enumerate(row):
                if v:
                    pygame.draw.rect(screen, KEY_TO_COLOR[kind], (panel_x + c*10, hy + r*10, 9, 9))

    # controls hint
    hint_y = HEIGHT - 200
    hints = ["Controls:", "←/→ Move", "↓ Soft drop", "↑ Rotate", "Z Rotate CCW", "Space Hard drop", "C Hold", "P Pause"]
    for i, h in enumerate(hints):
        screen.blit(font.render(h, True, WHITE), (panel_x, hint_y + i*18))

# ----- Main loop -----
def main():
    pygame.init()
    screen = pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption("Pytris")
    clock = pygame.time.Clock()
    font = pygame.font.SysFont("Consolas", 21)

    state = GameState()

    last_input = 0
    soft_hold = False

    while True:
        dt = clock.tick(FPS)
        for ev in pygame.event.get():
            if ev.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            elif ev.type == pygame.KEYDOWN:
                match ev.key:
                    case pygame.K_ESCAPE:
                        pygame.quit(); sys.ext()
                    case pygame.K_p:
                        state.paused = not state.paused
                    case pygame.K_c:
                        state.hold_action()
                    case pygame.K_z:
                        state.try_rotate_with_kick(cw=False)
                    case pygame.K_r:
                        state = GameState()
                    case pygame.K_SPACE:
                        state.hard_drop()
                    case pygame.K_UP:
                        state.try_rotate_with_kick(cw=True)
                    case pygame.K_DOWN:
                        state.soft_drop()
                    case pygame.K_LEFT:
                        if not state.collision(state.active, -1, 0):
                            state.active.x -= 1
                            if state.grounded:
                                state.reset_lock_timer()
                    case pygame.K_RIGHT:
                        if not state.collision(state.active, 1, 0):
                            state.active.x += 1
                            if state.grounded:
                                state.reset_lock_timer()
                    case pygame.K_w:
                        state.try_rotate_with_kick(cw=True)
                    case pygame.K_s:
                        state.soft_drop()
                    case pygame.K_a:
                        if not state.collision(state.active, -1, 0):
                            state.active.x -= 1
                            if state.grounded:
                                state.reset_lock_timer()
                    case pygame.K_d:
                        if not state.collision(state.active, 1, 0):
                            state.active.x += 1
                            if state.grounded:
                                state.reset_lock_timer()
        # gravity / tick
        state.tick()

        # draw
        screen.fill(BLACK)
        draw_board(screen, state)
        # ghost
        draw_ghost(screen, state)
        # active piece
        draw_piece(screen, state.active, ghost=False)
        # side panel
        draw_side_panel(screen, state, font)

        # game over text
        if state.game_over:
            go_txt = font.render("GAME OVER - R to restart", True, (255,40,40))
            screen.blit(go_txt, (PLAY_WIDTH//2 - 120, HEIGHT//2 - 10))

        pygame.display.flip()

if __name__ == "__main__":
    main()
