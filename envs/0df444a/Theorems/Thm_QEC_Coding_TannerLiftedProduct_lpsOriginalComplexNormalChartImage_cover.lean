-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalChartImage_cover
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalChartImage_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:09:40.188213+00:00
-- url     : https://prove2.me/theorems/a6f3354d-4818-4ac7-8445-9168908696f7
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Chart Image cover
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Chart Image cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialImages.lean#L27-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialImages.lean#L27-L35

import Definitions.Def_QEC_Coding_AlgebraicGeometry_SchemeOverlapImages
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialImages
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalOverlapImageOpenImmersion
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalChartImageOpenImmersion

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalChartImage_cover :
    lpsOriginalComplexNormalChartImage N hpos false ⊔
      lpsOriginalComplexNormalChartImage N hpos true = ⊤ := by sorry
