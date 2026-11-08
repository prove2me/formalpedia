-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_polynomialSchedule_rateRatio
-- name    : QEC.Coding.TannerLiftedProduct.polynomialSchedule_rateRatio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:08:44.278203+00:00
-- url     : https://prove2.me/theorems/760c6fa2-3c62-4aa6-ad72-9cd16818b399
-- title:
--   Tanner Lifted Product: polynomial Schedule rate Ratio
-- statement:
--   The semantic rate inequality for linearly scaled local dimensions is
--   exactly its coefficient-level inequality; the common `n^12` factor is
--   nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L575-L588
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L575-L588

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

theorem QEC.Coding.TannerLiftedProduct.polynomialSchedule_rateRatio
    (A B B' n : Nat) (rate : ℝ)
    (hCoefficient :
      2 * ((B : ℝ) + B') * A ≤
        (1 - rate) * ((A : ℝ) ^ 2 + 4 * B * B')) :
    2 * (((B * n ^ 6 : Nat) : ℝ) + (B' * n ^ 6 : Nat)) *
        ((A * n ^ 6 : Nat) : ℝ) ≤
      (1 - rate) *
        (((A * n ^ 6 : Nat) : ℝ) ^ 2 +
          4 * ((B * n ^ 6 : Nat) : ℝ) * (B' * n ^ 6 : Nat)) := by sorry
