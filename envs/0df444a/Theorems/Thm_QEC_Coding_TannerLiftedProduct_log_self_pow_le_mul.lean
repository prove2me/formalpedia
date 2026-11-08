-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_log_self_pow_le_mul
-- name    : QEC.Coding.TannerLiftedProduct.log_self_pow_le_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:48:46.692755+00:00
-- url     : https://prove2.me/theorems/27dcab32-46be-44ad-9f48-1734a6d08bc4
-- title:
--   Tanner Lifted Product: log self pow le mul
-- statement:
--   Logarithm of a fixed polynomial power grows at most linearly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L72-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L72-L76

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

theorem QEC.Coding.TannerLiftedProduct.log_self_pow_le_mul
    (q n a : Nat) (hq : 2 ≤ q) :
    Nat.log q (n ^ a) ≤ n * a := by sorry
