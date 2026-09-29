-- Prove2me | Theorems.Thm_Rudin_ch05_local_max_deriv_zero
-- name    : Rudin.ch05_local_max_deriv_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:04:47.602432+00:00
-- url     : https://prove2.me/theorems/110f7206-f42d-464b-9a00-a8d381da315a
-- title:
--   Theorem 5.8 — interior extrema have vanishing derivative
-- statement:
--   Let $f$ be defined on $[a,b]$. If $f$ has a local maximum at a point $x \in (a,b)$ and $f'(x)$ exists, then $f'(x) = 0$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, p. 107, Definition 5.7 and Theorem 5.8

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.8: if `f` has a local maximum at an interior point `x` of `[a, b]` and
`f'(x)` exists, then `f'(x) = 0`. -/
theorem ch05_local_max_deriv_zero (a b : ℝ) (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ Set.Ioo a b)
    (hmax : ∃ δ > 0, ∀ t ∈ Set.Ioo a b, |t - x| < δ → f t ≤ f x)
    (hdiff : DifferentiableAt ℝ f x) : deriv f x = 0 := by sorry

end Rudin
