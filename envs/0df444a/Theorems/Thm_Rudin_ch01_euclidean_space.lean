-- Prove2me | Theorems.Thm_Rudin_ch01_euclidean_space
-- name    : Rudin.ch01_euclidean_space
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:42:38.039276+00:00
-- url     : https://prove2.me/theorems/32e6602c-50f4-4aca-8115-00a5a91670a2
-- title:
--   Theorem 1.37 — euclidean space $\mathbb{R}^k$
-- statement:
--   In euclidean $k$-space: $|x| \ge 0$, with $|x| = 0$ only for $x = 0$; $|cx| = |c|\,|x|$ for real $c$; $|x \cdot y| \le |x||y|$; $|x + y| \le |x| + |y|$; and $|x - z| \le |x - y| + |y - z|$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 1, p. 16, Theorem 1.37

import Mathlib

namespace Rudin

/-- Rudin, Theorem 1.37: the basic metric properties of euclidean space `ℝ^k`: positivity and
nondegeneracy of the norm, homogeneity, the Schwarz inequality for the inner product, the
triangle inequality, and the three-point inequality `‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖`. -/
theorem ch01_euclidean_space (k : ℕ) (x y z : EuclideanSpace ℝ (Fin k)) (c : ℝ) :
    0 ≤ ‖x‖ ∧
    (‖x‖ = 0 ↔ x = 0) ∧
    ‖c • x‖ = |c| * ‖x‖ ∧
    |inner ℝ x y| ≤ ‖x‖ * ‖y‖ ∧
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ ∧
    ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by sorry

end Rudin
