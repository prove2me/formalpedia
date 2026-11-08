-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_log_le_exponent_of_le_pow
-- name    : QEC.Coding.TannerLiftedProduct.log_le_exponent_of_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:48:10.495385+00:00
-- url     : https://prove2.me/theorems/1cf8200e-f02c-44a1-a499-49eb89c17931
-- title:
--   Tanner Lifted Product: log le exponent of le pow
-- statement:
--   A power upper bound turns directly into an upper bound on the natural
--   logarithm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L64-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L64-L69

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

theorem QEC.Coding.TannerLiftedProduct.log_le_exponent_of_le_pow
    (q x e : Nat) (hq : 1 < q) (hPower : x ≤ q ^ e) :
    Nat.log q x ≤ e := by sorry
