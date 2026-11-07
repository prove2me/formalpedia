-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedTaylor_zero_of_nome
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedTaylor_zero_of_nome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:25:59.1023+00:00
-- url     : https://prove2.me/theorems/d3deda00-4015-45d5-9703-d82a965612a7
-- title:
--   Tanner Lifted Product: lps Original Analytic Cusp Localized Taylor zero of nome
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Cusp Localized Taylor zero of nome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L89-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L89-L108

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedTaylor_zero_of_nome
    (A : lpsOriginalAnalyticCuspLaurentRing)
    (hA : ∀ τ : ℍ,lpsOriginalAnalyticCuspLocalizedNomeEval τ A=0) :
    lpsOriginalAnalyticCuspLocalizedTaylor A=0 := by sorry
