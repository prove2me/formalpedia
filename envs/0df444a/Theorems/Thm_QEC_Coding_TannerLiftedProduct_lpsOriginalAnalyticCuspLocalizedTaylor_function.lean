-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedTaylor_function
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedTaylor_function
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:26:22.559502+00:00
-- url     : https://prove2.me/theorems/fc7c45cf-908f-4e55-bb05-50e61fe05b37
-- title:
--   Tanner Lifted Product: lps Original Analytic Cusp Localized Taylor function
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Cusp Localized Taylor function property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L51-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L51-L57

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedTaylor_function
    (F : lpsOriginalCuspAnalyticSubring) :
    lpsOriginalAnalyticCuspLocalizedTaylor
      (algebraMap lpsOriginalCuspAnalyticSubring lpsOriginalAnalyticCuspLaurentRing F)=
      algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing
        (lpsOriginalCuspTaylorRingHom F) := by sorry
