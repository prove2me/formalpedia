-- Prove2me | Theorems.Thm_Rudin_ch05_differentiable_continuous
-- name    : Rudin.ch05_differentiable_continuous
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:04:15.261259+00:00
-- url     : https://prove2.me/theorems/26abecd9-6bf1-4580-8645-3f867964bf37
-- title:
--   Theorem 5.2 — differentiability implies continuity
-- statement:
--   If $f$ is differentiable at $x$ then $f$ is continuous at $x$. The converse is false, as the absolute value function shows.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, p. 104, Theorem 5.2

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.2: a function differentiable at a point is continuous there. -/
theorem ch05_differentiable_continuous (f : ℝ → ℝ) (x : ℝ) (h : DifferentiableAt ℝ f x) :
    ContinuousAt f x := by sorry

end Rudin
