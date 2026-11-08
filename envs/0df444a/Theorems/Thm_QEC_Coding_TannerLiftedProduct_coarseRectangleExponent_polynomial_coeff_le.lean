-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleExponent_polynomial_coeff_le
-- name    : QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_polynomial_coeff_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:48:13.810122+00:00
-- url     : https://prove2.me/theorems/65f9ac14-d0dd-4d25-9e80-b0abd62737fb
-- title:
--   Tanner Lifted Product: coarse Rectangle Exponent polynomial coeff le
-- statement:
--   Coefficient-bearing version of the PK22 polynomial schedule:
--   `w = A n^6`, `m = M n^4`, and `s = S n^7`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L184-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L184-L224

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

theorem QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_polynomial_coeff_le
    (A M S n q : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hn : 0 < n) :
    coarseRectangleExponent
        (A * n ^ 6) (M * n ^ 4) (S * n ^ 7) q + 3 ≤
      (2 * A + 2 * A * S + 4 * M * A + 16 * S + 11) * n ^ 10 := by sorry
