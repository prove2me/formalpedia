-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_cpow_finset_boundary_product
-- name    : WeightedRootIntegralIdentity.cpow_finset_boundary_product
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-13T15:02:27.685983+00:00
-- url     : https://prove2.me/theorems/11b0d24d-26be-4932-b71b-fc742b4c8aed
-- title:
--   Boundary phase of a finite product of complex powers
-- statement:
--   Let $s$ be a finite index set, and let $f_i\ne0$ and $w_i\in\mathbb R$. For principal complex powers of the real numbers $f_i$,
--
--   $$
--   \prod_{i\in s} f_i^{w_i}
--   =
--   \left(\prod_{i\in s} |f_i|^{w_i}\right)
--   \exp\left(i\pi\sum_{\substack{i\in s\\ f_i<0}}w_i\right).
--   $$
--
--   Thus the magnitude is the product of the real powers of the absolute values, while every negative factor contributes the phase $e^{i\pi w_i}$. This is the finite-product boundary calculation used to derive the jump across each branch-cut interval.
-- source:
--   Finite-product form of the boundary phase calculation in https://math.stackexchange.com/questions/4244874/can-we-prove-am-gm-inequality-using-these-integrals, first answer, equations describing the upper and lower boundary values before the sine-weighted jump.

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_negative_real_boundary
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem cpow_finset_boundary_product
    {ι : Type} [DecidableEq ι] (s : Finset ι) (f w : ι → ℝ)
    (hzero : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, ((f i : ℂ) ^ (w i : ℂ))) =
      ((∏ i ∈ s, Real.rpow |f i| (w i) : ℝ) : ℂ) *
        Complex.exp
          ((((Real.pi * (∑ i ∈ s.filter (fun j => f j < 0), w i) : ℝ) : ℝ) : ℂ) *
            Complex.I) := by sorry

end WeightedRootIntegralIdentity
