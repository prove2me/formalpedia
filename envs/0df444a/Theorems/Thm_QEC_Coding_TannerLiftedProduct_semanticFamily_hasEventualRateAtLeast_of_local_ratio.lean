-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_semanticFamily_hasEventualRateAtLeast_of_local_ratio
-- name    : QEC.Coding.TannerLiftedProduct.semanticFamily_hasEventualRateAtLeast_of_local_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:21:06.740955+00:00
-- url     : https://prove2.me/theorems/1cd393e6-25f3-428a-a5b9-d4b896ad764e
-- title:
--   Tanner Lifted Product: semantic Family has Eventual Rate At Least of local ratio
-- statement:
--   A single local-dimension ratio gives the requested rate bound at every
--   member of the cofinal semantic Tanner family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L207-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L207-L222

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

theorem QEC.Coding.TannerLiftedProduct.semanticFamily_hasEventualRateAtLeast_of_local_ratio
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a))
    (rate : ℝ)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    QEC.QLDPC.HasEventualRateAtLeast
      (semanticFamily label h h' hW hGroupCofinal) rate := by sorry
