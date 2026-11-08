-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_canonicalRelativeDistance_mul_blockLength_le
-- name    : QEC.Coding.TannerLiftedProduct.canonicalRelativeDistance_mul_blockLength_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:21:57.473288+00:00
-- url     : https://prove2.me/theorems/47d5122f-085f-41bf-8312-8a02d2cda127
-- title:
--   Tanner Lifted Product: canonical Relative Distance mul block Length le
-- statement:
--   The canonical radius lower bound is a fixed positive fraction of the
--   actual semantic block length, uniformly over the voltage group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L122-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L122-L169

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

theorem QEC.Coding.TannerLiftedProduct.canonicalRelativeDistance_mul_blockLength_le
    (a : A) (label : W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W) :
    canonicalRelativeDistance (W := W) (R := R) (R' := R') *
        ((semanticPresentation label h h').blockLength : ℝ) ≤
      (canonicalRadius (W := W) (G := G) a /
          (2 * Fintype.card W) + 1 : Nat) := by sorry
