-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedTaylor_invParameter
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedTaylor_invParameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:26:06.788281+00:00
-- url     : https://prove2.me/theorems/bdf90932-676e-491a-8395-642df04f5d0f
-- title:
--   Tanner Lifted Product: lps Original Analytic Cusp Localized Taylor inv Parameter
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Cusp Localized Taylor inv Parameter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L126-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L126-L140

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedTaylor_invParameter :
    lpsOriginalAnalyticCuspLocalizedTaylor
      (IsLocalization.Away.invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
        lpsOriginalAnalyticCuspLaurentParameter)=
      IsLocalization.Away.invSelf (S:=lpsOriginalComplexCuspLaurentRing)
        (PowerSeries.X : PowerSeries ℂ) := by sorry
