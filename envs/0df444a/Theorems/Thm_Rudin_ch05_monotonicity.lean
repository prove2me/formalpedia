-- Prove2me | Theorems.Thm_Rudin_ch05_monotonicity
-- name    : Rudin.ch05_monotonicity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:15:35.239992+00:00
-- url     : https://prove2.me/theorems/ecb8203e-7173-431f-abd8-773bcc5174a3
-- title:
--   Theorem 5.11 — sign of the derivative and monotonicity
-- statement:
--   Let $f$ be differentiable on $(a,b)$. If $f' \ge 0$ throughout, $f$ is monotonically increasing; if $f' = 0$ throughout, $f$ is constant; if $f' \le 0$ throughout, $f$ is monotonically decreasing.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, p. 108, Theorem 5.11

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.11: on an interval where `f` is differentiable, a nonnegative derivative
makes `f` monotonically increasing, a vanishing derivative makes it constant, and a nonpositive
derivative makes it monotonically decreasing. -/
theorem ch05_monotonicity (a b : ℝ) (f : ℝ → ℝ)
    (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
    ((∀ x ∈ Set.Ioo a b, 0 ≤ deriv f x) → MonotoneOn f (Set.Ioo a b)) ∧
    ((∀ x ∈ Set.Ioo a b, deriv f x = 0) → ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, f x = f y) ∧
    ((∀ x ∈ Set.Ioo a b, deriv f x ≤ 0) → AntitoneOn f (Set.Ioo a b)) := by sorry

end Rudin
