-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalToIntegerBaseChange_chart
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalToIntegerBaseChange_chart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:00:59.622297+00:00
-- url     : https://prove2.me/theorems/c0ba6c09-b42f-4f5d-9787-256034c2e312
-- title:
--   Tanner Lifted Product: lps Original Complex Normal To Integer Base Change chart
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal To Integer Base Change chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L336-L359
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L336-L359

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalToIntegerBaseChange_chart
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    lpsOriginalComplexNormalGluedChartMap N hN b ≫
      lpsOriginalComplexNormalToIntegerBaseChange N hN =
    (lpsOriginalComplexNormalChartBaseChangeIso N hN b).hom ≫
      (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f b := by sorry
