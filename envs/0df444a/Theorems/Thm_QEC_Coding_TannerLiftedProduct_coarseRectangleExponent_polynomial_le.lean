-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleExponent_polynomial_le
-- name    : QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_polynomial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:02.644811+00:00
-- url     : https://prove2.me/theorems/8cd31142-3308-4b60-9e3c-f3f8aa789883
-- title:
--   Tanner Lifted Product: coarse Rectangle Exponent polynomial le
-- statement:
--   For the PK22 polynomial schedule `w = A n^6`, `m = n^4`, `s = n^7`,
--   the rectangle exponent is bounded by a constant times `n^10`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L144-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L144-L180

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

theorem QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_polynomial_le
    (A n q : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hn : 0 < n) :
    coarseRectangleExponent (A * n ^ 6) (n ^ 4) (n ^ 7) q + 3 ≤
      (8 * A + 26) * n ^ 10 := by sorry
