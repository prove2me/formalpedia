-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleFactor_le_power
-- name    : QEC.Coding.TannerLiftedProduct.coarseRectangleFactor_le_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:56.988425+00:00
-- url     : https://prove2.me/theorems/1f7be569-9a02-4684-9f3e-250858e8f703
-- title:
--   Tanner Lifted Product: coarse Rectangle Factor le power
-- statement:
--   The coarse rectangle factor is at most one explicit power of the field
--   size.  Logarithms retain the sublinear `s log w` contribution instead of
--   replacing it by the unusable `s w` bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L328-L368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L328-L368

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

theorem QEC.Coding.TannerLiftedProduct.coarseRectangleFactor_le_power
    (w m s q : Nat) (hq : 2 ≤ q) :
    coarseRectangleFactor w m s q ≤
      q ^ coarseRectangleExponent w m s q := by sorry
