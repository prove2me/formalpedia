-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_polynomialSchedule_realBudget
-- name    : QEC.Coding.TannerLiftedProduct.polynomialSchedule_realBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:51:49.537415+00:00
-- url     : https://prove2.me/theorems/372233a9-0754-4a00-9d97-949dfafa35a1
-- title:
--   Tanner Lifted Product: polynomial Schedule real Budget
-- statement:
--   The real-valued product-expansion budget for the polynomial schedule
--   follows from the integer coefficient bound `18 ≤ D n^2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L467-L491
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L467-L491

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

theorem QEC.Coding.TannerLiftedProduct.polynomialSchedule_realBudget
    (A D n : Nat) (hA : 0 < A) (hn : 0 < n)
    (hBudget : 18 ≤ D * n ^ 2) :
    4 * (n ^ 4 : ℝ) + 2 ≤
      ((D * n ^ 6 : Nat) : ℝ) /
          (3 * ((A * n ^ 6 : Nat) : ℝ)) *
        ((A * n ^ 6 : Nat) : ℝ) := by sorry
