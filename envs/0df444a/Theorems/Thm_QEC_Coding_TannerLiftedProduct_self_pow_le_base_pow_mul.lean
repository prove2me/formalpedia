-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_self_pow_le_base_pow_mul
-- name    : QEC.Coding.TannerLiftedProduct.self_pow_le_base_pow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:47:55.924565+00:00
-- url     : https://prove2.me/theorems/82f020b9-fb75-4116-b8da-903c792a8c36
-- title:
--   Tanner Lifted Product: self pow le base pow mul
-- statement:
--   Polynomial powers can be absorbed into an exponential with a linear
--   exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L55-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L55-L60

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

theorem QEC.Coding.TannerLiftedProduct.self_pow_le_base_pow_mul (q n a : Nat) (hq : 2 ≤ q) :
    n ^ a ≤ q ^ (n * a) := by sorry
