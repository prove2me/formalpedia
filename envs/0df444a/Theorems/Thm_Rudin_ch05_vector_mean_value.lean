-- Prove2me | Theorems.Thm_Rudin_ch05_vector_mean_value
-- name    : Rudin.ch05_vector_mean_value
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:11:58.521318+00:00
-- url     : https://prove2.me/theorems/7e6851fb-17f8-439a-aba0-7953cb6bf9f0
-- title:
--   Theorem 5.19 — mean value inequality for vector-valued functions
-- statement:
--   If $\mathbf{f}$ is a continuous mapping of $[a,b]$ into $\mathbb{R}^k$ which is differentiable on $(a,b)$, then there is $x \in (a,b)$ with $\|\mathbf{f}(b) - \mathbf{f}(a)\| \le (b-a)\,\|\mathbf{f}'(x)\|$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, p. 113, Theorem 5.19

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.19: if `f` is a continuous mapping of `[a, b]` into `ℝ^k`, differentiable
on `(a, b)`, then there is `x ∈ (a, b)` with `‖f b - f a‖ ≤ (b - a) * ‖f'(x)‖`. -/
theorem ch05_vector_mean_value (k : ℕ) (a b : ℝ) (hab : a < b)
    (f : ℝ → EuclideanSpace ℝ (Fin k))
    (hfc : ContinuousOn f (Set.Icc a b)) (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
    ∃ x ∈ Set.Ioo a b, ‖f b - f a‖ ≤ (b - a) * ‖deriv f x‖ := by sorry

end Rudin
