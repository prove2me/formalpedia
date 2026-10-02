-- Prove2me | Theorems.Thm_TheoryOfGames_Minimax_alternative_strict
-- name    : TheoryOfGames.Minimax.alternative_strict
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T03:21:55.446864+00:00
-- url     : https://prove2.me/theorems/b73a4fda-dd75-4379-a09a-f5d93c2a87f4
-- title:
--   (16:C) — theorem of the alternative for matrices (strict form)
-- statement:
--   Let $a(i, j)$, $i = 1, \dots, n$, $j = 1, \dots, m$, be a real matrix with $n \ge 1$ rows and $m \ge 1$ columns, and let $S_k$ denote the simplex of probability vectors in $\mathbb R^k$. Then exactly one of the following holds:
--
--   1. (16:16:a) there is $x = (x_1, \dots, x_m) \in S_m$ with
--   $$\sum_{j=1}^m a(i, j)\, x_j \le 0 \quad \text{for } i = 1, \dots, n;$$
--   2. (16:16:b) there is $w = (w_1, \dots, w_n) \in S_n$ with
--   $$\sum_{i=1}^n a(i, j)\, w_i > 0 \quad \text{for } j = 1, \dots, m.$$
--
--   The existence of one of the two alternatives is (16:C); that they exclude each other is the observation stated immediately after it. This is the convexity result from which the book derives the minimax theorem (via (16:F)).
--
--   **Formalization Note** Rows and columns are indexed from $0$ (`Fin n`, `Fin m`). "Exactly one" is `Xor` of the two existence statements.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 140, (16:C) and the following observation

import Mathlib

namespace TheoryOfGames.Minimax

/-- (16:C), p. 140, with the observation after it: for a real matrix `a(i, j)` with `n ≥ 1`
rows and `m ≥ 1` columns, exactly one of the following holds: there is `x ∈ S_m` with
`∑_j a(i, j) x_j ≤ 0` for every row `i` (16:16:a), or there is `w ∈ S_n` with
`∑_i a(i, j) w_i > 0` for every column `j` (16:16:b). -/
theorem alternative_strict {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (a : Fin n → Fin m → ℝ) :
    Xor (∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0)
      (∃ w ∈ stdSimplex ℝ (Fin n), ∀ j, 0 < ∑ i, a i j * w i) := by sorry

end TheoryOfGames.Minimax
