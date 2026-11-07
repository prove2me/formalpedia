-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspAffineBranch_taylor
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspAffineBranch_taylor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:26:12.090443+00:00
-- url     : https://prove2.me/theorems/aad773b1-7a9a-499b-a915-a7770625034e
-- title:
--   Tanner Lifted Product: lps Original Analytic Cusp Affine Branch taylor
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Analytic Cusp Affine Branch taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L166-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAnalyticCuspLocalization.lean#L166-L185

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspAffineBranch_taylor (m : ℕ) (hm : 0<m) (r : ℚ) :
    lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticCuspAffineBranch m hm r)=
      (IsLocalization.Away.invSelf (S:=lpsOriginalComplexCuspLaurentRing)
        (PowerSeries.X : PowerSeries ℂ))^m *
        algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing
          (PowerSeries.C ((Function.Periodic.qParam 1 (r:ℂ))⁻¹) *
            PowerSeries.expand m hm.ne' (PowerSeries.rescale (Function.Periodic.qParam 1 (r:ℂ))
              (lpsOriginalTaylorSeries lpsOriginalJQCoefficient))) := by sorry
