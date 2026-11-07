-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedNomeEval_function
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedNomeEval_function
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:25:54.770586+00:00
-- url     : https://prove2.me/theorems/80a9b73e-d8c2-4a7c-8cd5-81eb6a7c4fff
-- title:
--   Tanner Lifted Product: lps Original Analytic Cusp Localized Nome Eval function
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Cusp Localized Nome Eval function property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L59-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L59-L64

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedNomeEval_function
    (τ : ℍ) (F : lpsOriginalCuspAnalyticSubring) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ
      (algebraMap lpsOriginalCuspAnalyticSubring lpsOriginalAnalyticCuspLaurentRing F)=
      F.val (Function.Periodic.qParam 1 (τ:ℂ)) := by sorry
