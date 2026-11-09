-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_exact_optimal_flooding_uniform_xp
-- name    : ThreeColorFloodIt.FixedHeight.exact_optimal_flooding_uniform_xp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:38.388067+00:00
-- url     : https://prove2.me/theorems/332ea57e-85d3-451b-91ba-a9ae495c09d6
-- title:
--   Theorem 3 — Uniform exact optimal flooding at every fixed height
-- statement:
--   There exist one deterministic finite multitape machine and absolute natural constants $C\ge1$, $a\ge1$, $b\ge0$, chosen before every height, width and coloring. For all $k,n\ge1$, writing $N=kn$, the machine returns both the exact free-flooding optimum $d=m(B)$ and an actual legal flooding sequence $L$ of exactly $d$ moves. Its charged running time satisfies
--   $$T(B)\le C N^{a k^2+b}\quad(N\ge2).$$
--   The one-vertex case returns zero and the empty sequence within $C$ steps. The same machine has, at height $k$, the bound
--   $$T(B)\le C k^{a k^2+b} n^{a k^2+b},$$
--   and satisfies the explicit XP predicate. Available colors are $\{0,1,2\}$; the input may use any subset, need not be proper, and the final color is unrestricted. Time includes reading the input, construction, bounded-cost arithmetic and writing every witness move. Neither an optimum value nor any fast optimization oracle is an input.
--
--   Differences from the source:
--   - encoding: deterministic N^{O(k²)} time and n^{O(k²)} time at every fixed height, with optimal count and sequence → one shared finite multitape machine and global C,a,b with time C·N^(a·k²+b), direct N=1 handling, an explicit fixed-height coefficient and XP predicate; reason: Section 5.1 makes the construction uniform and bounds height-only factors by 2^{O(k² log(k+1))}; existential absolute exponent constants preserve precisely the asymptotic claim
--   - encoding: complete k by n boards with at most three colors and vertex/color moves → zero-based Fin k × Fin n, three available color labels, binary row-major input and full encoded move triples; reason: injective relabeling covers palettes using fewer colors; coordinates take logarithmically many bits and the exact legal witness is output
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 5 (PDF 6), Theorem 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_machine

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem exact_optimal_flooding_uniform_xp :
    ∃ (A : IntMul.MultitapeTM) (C a b : ℕ), 1 ≤ C ∧ 1 ≤ a ∧
      (∀ (k n : ℕ), 0 < k → 0 < n → ∀ f : Board k n,
        ∃ (t d : ℕ) (ms : List (Move (Cell k n) (Fin 3))),
          A.HaltsWithOutputW (boardInput f) t (floodingOutput d ms) ∧
          ExactOutput f d ms ∧
          t ≤ (if k * n = 1 then C else C * (k * n) ^ (a * k ^ 2 + b)) ∧
          (k * n = 1 → d = 0 ∧ ms = []) ∧
          t ≤ (C * k ^ (a * k ^ 2 + b)) * n ^ (a * k ^ 2 + b)) ∧
      FloodingXP A := by sorry

end ThreeColorFloodIt.FixedHeight
