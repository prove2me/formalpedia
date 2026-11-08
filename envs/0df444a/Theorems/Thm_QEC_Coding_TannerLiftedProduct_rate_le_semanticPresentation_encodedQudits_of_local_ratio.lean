-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rate_le_semanticPresentation_encodedQudits_of_local_ratio
-- name    : QEC.Coding.TannerLiftedProduct.rate_le_semanticPresentation_encodedQudits_of_local_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:46:40.43196+00:00
-- url     : https://prove2.me/theorems/bb5535d3-35d0-4520-8201-b253389461ce
-- title:
--   Tanner Lifted Product: rate le semantic Presentation encoded Qudits of local ratio
-- statement:
--   The source local-dimension ratio is already a rate bound for the actual
--   semantic Tanner presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L104-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L104-L117

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_24

theorem QEC.Coding.TannerLiftedProduct.rate_le_semanticPresentation_encodedQudits_of_local_ratio
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (rate : ℝ)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    rate * ((semanticPresentation label h h').blockLength : ℝ) ≤
      ((semanticPresentation label h h').encodedQudits : ℝ) := by sorry
