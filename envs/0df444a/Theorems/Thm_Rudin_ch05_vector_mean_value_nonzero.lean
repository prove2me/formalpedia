-- Prove2me | Theorems.Thm_Rudin_ch05_vector_mean_value_nonzero
-- name    : Rudin.ch05_vector_mean_value_nonzero
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-13T13:18:35.538517+00:00
-- url     : https://prove2.me/theorems/115f3307-a00e-4dce-992b-2007cbf872fd
-- title:
--   Non-degenerate vector mean value inequality
-- statement:
--   Let $f:[a,b] \to \mathbb R^k$ be continuous on the closed interval and differentiable on its interior, with $a<b$. Assume that its endpoint displacement is nonzero. Then there is a point $x\in(a,b)$ such that
--
--   $$\lVert f(b)-f(a)\rVert\le(b-a)\lVert f'(x)\rVert.$$
--
--   This is the non-degenerate branch of Rudin’s vector-valued mean value inequality. Separating it from the zero-displacement case isolates the scalarization argument along the endpoint-displacement direction.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., Chapter 5, p. 113, Theorem 5.19

import Mathlib

open Filter Topology

namespace Rudin

/-- Non-degenerate case of Rudin, Theorem 5.19. -/
theorem ch05_vector_mean_value_nonzero (k : ℕ) (a b : ℝ) (hab : a < b)
    (f : ℝ → EuclideanSpace ℝ (Fin k))
    (hfc : ContinuousOn f (Set.Icc a b)) (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
    (hneq : f b - f a ≠ 0) :
    ∃ x ∈ Set.Ioo a b, ‖f b - f a‖ ≤ (b - a) * ‖deriv f x‖ := by sorry

end Rudin
