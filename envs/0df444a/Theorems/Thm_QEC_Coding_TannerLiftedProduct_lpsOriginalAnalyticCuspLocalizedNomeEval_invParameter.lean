-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedNomeEval_invParameter
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedNomeEval_invParameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:27:33.293585+00:00
-- url     : https://prove2.me/theorems/cc25ee63-914c-4f04-ab5a-e6c75a85fb10
-- title:
--   Tanner Lifted Product: lps Original Analytic Cusp Localized Nome Eval inv Parameter
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Cusp Localized Nome Eval inv Parameter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L110-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L110-L124

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedNomeEval_invParameter (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ
      (IsLocalization.Away.invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
        lpsOriginalAnalyticCuspLaurentParameter)=
      (Function.Periodic.qParam 1 (τ:ℂ))⁻¹ := by sorry
