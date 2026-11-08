-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rectangleFactor_lt_of_exponent
-- name    : QEC.Coding.TannerLiftedProduct.rectangleFactor_lt_of_exponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:51.628228+00:00
-- url     : https://prove2.me/theorems/8ba6d98a-9048-4d5b-8202-29542f09290a
-- title:
--   Tanner Lifted Product: rectangle Factor lt of exponent
-- statement:
--   An exponent comparison implies the exact sparse-rectangle bad-event
--   budget, including its factor `6`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L372-L395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L372-L395

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_24
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_25

theorem QEC.Coding.TannerLiftedProduct.rectangleFactor_lt_of_exponent
    (w m s q target : Nat) (hq : 2 ≤ q)
    (hExponent : coarseRectangleExponent w m s q + 3 < target) :
    6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
      (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * w + s))) < q ^ target := by sorry
