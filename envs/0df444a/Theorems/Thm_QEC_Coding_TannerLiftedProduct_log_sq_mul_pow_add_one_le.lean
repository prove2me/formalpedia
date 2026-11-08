-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_log_sq_mul_pow_add_one_le
-- name    : QEC.Coding.TannerLiftedProduct.log_sq_mul_pow_add_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:48:17.729316+00:00
-- url     : https://prove2.me/theorems/4038a364-cddf-482f-8018-4370f912c2e9
-- title:
--   Tanner Lifted Product: log sq mul pow add one le
-- statement:
--   The logarithm of the squared local length `(A * n^e)^2 + 1` has an
--   explicit linear bound in `A` and `n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L92-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L92-L127

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

theorem QEC.Coding.TannerLiftedProduct.log_sq_mul_pow_add_one_le
    (q A n e : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hn : 0 < n) :
    Nat.log q ((A * n ^ e) * (A * n ^ e) + 1) ≤
      2 * (A + n * e) + 1 := by sorry
