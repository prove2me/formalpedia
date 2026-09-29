-- Prove2me | Theorems.Thm_Rudin_ch05_mean_value
-- name    : Rudin.ch05_mean_value
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:13:36.166013+00:00
-- url     : https://prove2.me/theorems/035a8689-f8c3-4048-916e-9f5bef5e89e2
-- title:
--   Theorem 5.10 — mean value theorem
-- statement:
--   If $f$ is a continuous real function on $[a,b]$ which is differentiable on $(a,b)$, then $f(b) - f(a) = (b-a) f'(x)$ for some $x \in (a,b)$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, p. 108, Theorem 5.10

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.10 (mean value theorem): if `f` is continuous on `[a, b]` and
differentiable on `(a, b)`, there is `x ∈ (a, b)` with `f b - f a = (b - a) * f'(x)`. -/
theorem ch05_mean_value (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Icc a b)) (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
    ∃ x ∈ Set.Ioo a b, f b - f a = (b - a) * deriv f x := by sorry

end Rudin
