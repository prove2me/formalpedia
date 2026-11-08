-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sq_add_one_pow_le_three_mul
-- name    : QEC.Coding.TannerLiftedProduct.sq_add_one_pow_le_three_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:40.342882+00:00
-- url     : https://prove2.me/theorems/53619209-e7d8-4106-bb9d-1dfce4946e9b
-- title:
--   Tanner Lifted Product: sq add one pow le three mul
-- statement:
--   The quadratic smoothing weight has only constant multiplicative loss:
--   `(A² + 1)^A ≤ 3 A^(2A)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L755-L788
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L755-L788

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

theorem QEC.Coding.TannerLiftedProduct.sq_add_one_pow_le_three_mul
    (A : Nat) (hA : 0 < A) :
    (A ^ 2 + 1) ^ A ≤ 3 * A ^ (2 * A) := by sorry
