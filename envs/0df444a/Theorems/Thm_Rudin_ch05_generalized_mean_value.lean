-- Prove2me | Theorems.Thm_Rudin_ch05_generalized_mean_value
-- name    : Rudin.ch05_generalized_mean_value
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:06:10.648103+00:00
-- url     : https://prove2.me/theorems/a58be856-e84b-4038-8136-fa5546e2034e
-- title:
--   Theorem 5.9 — generalized mean value theorem
-- statement:
--   If $f$ and $g$ are continuous real functions on $[a,b]$ which are differentiable on $(a,b)$, then there is a point $x \in (a,b)$ at which $(f(b) - f(a))\,g'(x) = (g(b) - g(a))\,f'(x)$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, p. 107, Theorem 5.9

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.9 (generalized mean value theorem): if `f` and `g` are continuous on
`[a, b]` and differentiable on `(a, b)`, there is `x ∈ (a, b)` with
`(f b - f a) * g'(x) = (g b - g a) * f'(x)`. -/
theorem ch05_generalized_mean_value (a b : ℝ) (hab : a < b) (f g : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b))
    (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
    (hgd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ g x) :
    ∃ x ∈ Set.Ioo a b, (f b - f a) * deriv g x = (g b - g a) * deriv f x := by sorry

end Rudin
