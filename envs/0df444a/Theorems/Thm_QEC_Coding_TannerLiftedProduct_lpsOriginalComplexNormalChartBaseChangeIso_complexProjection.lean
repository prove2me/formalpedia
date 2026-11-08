-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalChartBaseChangeIso_complexProjection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalChartBaseChangeIso_complexProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:04:32.390426+00:00
-- url     : https://prove2.me/theorems/b1cdc532-b904-4071-a5c1-fcfa5c687977
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Chart Base Change Iso complex Projection
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Chart Base Change Iso complex Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L313-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L313-L327

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalChartBaseChangeIso_complexProjection
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    (lpsOriginalComplexNormalChartBaseChangeIso N hN b).hom ≫ pullback.fst _ _ =
      lpsOriginalComplexChartToSpecC N hN b := by sorry
