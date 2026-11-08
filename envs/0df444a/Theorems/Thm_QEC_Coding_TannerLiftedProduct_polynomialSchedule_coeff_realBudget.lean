-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_polynomialSchedule_coeff_realBudget
-- name    : QEC.Coding.TannerLiftedProduct.polynomialSchedule_coeff_realBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:52:32.257342+00:00
-- url     : https://prove2.me/theorems/aaaac6ea-9717-4db8-81f8-384559bbaace
-- title:
--   Tanner Lifted Product: polynomial Schedule coeff real Budget
-- statement:
--   Coefficient-bearing real product-expansion budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L494-L520
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L494-L520

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

theorem QEC.Coding.TannerLiftedProduct.polynomialSchedule_coeff_realBudget
    (A D M n : Nat) (hA : 0 < A) (hn : 0 < n)
    (hBudget : 12 * M + 6 ≤ D * n ^ 2) :
    4 * ((M * n ^ 4 : Nat) : ℝ) + 2 ≤
      ((D * n ^ 6 : Nat) : ℝ) /
          (3 * ((A * n ^ 6 : Nat) : ℝ)) *
        ((A * n ^ 6 : Nat) : ℝ) := by sorry
