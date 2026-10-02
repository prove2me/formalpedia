-- Prove2me | Theorems.Thm_TheoryOfGames_Minimax_alternative_weak
-- name    : TheoryOfGames.Minimax.alternative_weak
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T03:24:22.735667+00:00
-- url     : https://prove2.me/theorems/12a41f1e-b2d6-4b29-abe8-dcb34edcfdcc
-- title:
--   (16:F) — theorem of the alternative for matrices (weak form)
-- statement:
--   Let $a(i, j)$, $i = 1, \dots, n$, $j = 1, \dots, m$, be a real matrix with $n \ge 1$ rows and $m \ge 1$ columns. Then there is $x \in S_m$ with
--   $$\sum_{j=1}^m a(i, j)\, x_j \le 0 \quad \text{for } i = 1, \dots, n \qquad \text{(16:19:a)},$$
--   or there is $w \in S_n$ with
--   $$\sum_{i=1}^n a(i, j)\, w_i \ge 0 \quad \text{for } j = 1, \dots, m \qquad \text{(16:19:b)}.$$
--
--   The two alternatives need not exclude each other (footnote 1 on p. 142). This is the form of the theorem of the alternative that the book applies, with $a = \mathcal H$, in 17.6 to prove the minimax theorem (17:6).
--
--   **Formalization Note** Rows and columns are indexed from $0$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 142, (16:F)

import Mathlib

namespace TheoryOfGames.Minimax

/-- (16:F), p. 142: for a real matrix `a(i, j)` with `n ≥ 1` rows and `m ≥ 1` columns, there
is `x ∈ S_m` with `∑_j a(i, j) x_j ≤ 0` for every row `i` (16:19:a), or there is `w ∈ S_n`
with `∑_i a(i, j) w_i ≥ 0` for every column `j` (16:19:b). -/
theorem alternative_weak {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (a : Fin n → Fin m → ℝ) :
    (∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0) ∨
      (∃ w ∈ stdSimplex ℝ (Fin n), ∀ j, 0 ≤ ∑ i, a i j * w i) := by sorry

end TheoryOfGames.Minimax
