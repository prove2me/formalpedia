-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_replicatedSchedule_rateRatio
-- name    : QEC.Coding.TannerLiftedProduct.replicatedSchedule_rateRatio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:17:45.161204+00:00
-- url     : https://prove2.me/theorems/6fd1d765-9b72-4a4c-b5d8-bcb2ee51cbb7
-- title:
--   Tanner Lifted Product: replicated Schedule rate Ratio
-- statement:
--   The semantic rate inequality is invariant under replication by an
--   arbitrary common positive-or-zero block count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L557-L570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L557-L570

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

theorem QEC.Coding.TannerLiftedProduct.replicatedSchedule_rateRatio
    (A B B' N : Nat) (rate : ℝ)
    (hCoefficient :
      2 * ((B : ℝ) + B') * A ≤
        (1 - rate) * ((A : ℝ) ^ 2 + 4 * B * B')) :
    2 * (((B * N : Nat) : ℝ) + (B' * N : Nat)) *
        ((A * N : Nat) : ℝ) ≤
      (1 - rate) *
        (((A * N : Nat) : ℝ) ^ 2 +
          4 * ((B * N : Nat) : ℝ) * (B' * N : Nat)) := by sorry
