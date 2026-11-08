-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rootSchedule_coeff_realBudget
-- name    : QEC.Coding.TannerLiftedProduct.rootSchedule_coeff_realBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:34:31.116713+00:00
-- url     : https://prove2.me/theorems/25786556-ad55-4cb3-8ae9-cde66171809c
-- title:
--   Tanner Lifted Product: root Schedule coeff real Budget
-- statement:
--   Real product-expansion budget for an arbitrary replicated block count
--   `N ≥ x^6`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L524-L553
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L524-L553

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_24

theorem QEC.Coding.TannerLiftedProduct.rootSchedule_coeff_realBudget
    (A D M N x : Nat) (hA : 0 < A) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N)
    (hBudget : 12 * M + 6 ≤ D * x ^ 2) :
    4 * ((M * x ^ 4 : Nat) : ℝ) + 2 ≤
      ((D * N : Nat) : ℝ) /
          (3 * ((A * N : Nat) : ℝ)) *
        ((A * N : Nat) : ℝ) := by sorry
