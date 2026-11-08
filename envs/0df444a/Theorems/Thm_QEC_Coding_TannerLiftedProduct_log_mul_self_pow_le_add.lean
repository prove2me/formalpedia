-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_log_mul_self_pow_le_add
-- name    : QEC.Coding.TannerLiftedProduct.log_mul_self_pow_le_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:48:07.88821+00:00
-- url     : https://prove2.me/theorems/66129e0e-a9df-4d25-b1db-c078e7a65941
-- title:
--   Tanner Lifted Product: log mul self pow le add
-- statement:
--   A constant coefficient and a polynomial power have a logarithm bounded
--   by the sum of their linear exponential budgets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L80-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L80-L88

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

theorem QEC.Coding.TannerLiftedProduct.log_mul_self_pow_le_add
    (q C n a : Nat) (hq : 2 ≤ q) :
    Nat.log q (C * n ^ a) ≤ C + n * a := by sorry
