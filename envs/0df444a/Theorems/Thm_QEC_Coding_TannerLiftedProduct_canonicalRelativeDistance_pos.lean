-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_canonicalRelativeDistance_pos
-- name    : QEC.Coding.TannerLiftedProduct.canonicalRelativeDistance_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:22:13.706865+00:00
-- url     : https://prove2.me/theorems/68b1564c-77ec-4724-8dd0-67f3f8ea7c5a
-- title:
--   Tanner Lifted Product: canonical Relative Distance pos
-- statement:
--   The canonical relative-distance constant is strictly positive whenever
--   the local direction type is nonempty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L115-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L115-L118

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerPairExistence
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {A F W R R' : Type u} {G : A → Type u}
variable [Field F] [Fintype F]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
variable [∀ a, Group (G a)] [∀ a, Fintype (G a)]
variable [∀ a, DecidableEq (G a)]
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_34
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_35
omit [DecidableEq W] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.canonicalRelativeDistance_pos (hW : 0 < Fintype.card W) :
    0 < canonicalRelativeDistance (W := W) (R := R) (R' := R') := by sorry
