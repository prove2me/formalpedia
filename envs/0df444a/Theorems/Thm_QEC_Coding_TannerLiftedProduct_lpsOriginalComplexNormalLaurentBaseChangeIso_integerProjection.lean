-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalLaurentBaseChangeIso_integerProjection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalLaurentBaseChangeIso_integerProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:59:44.735486+00:00
-- url     : https://prove2.me/theorems/2ef4549a-6b26-4ec9-bfab-6aa355d88ed9
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Laurent Base Change Iso integer Projection
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Laurent Base Change Iso integer Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L379-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L379-L385

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalLaurentBaseChangeIso_integerProjection
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalComplexNormalLaurentBaseChangeIso N hN).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (lpsOriginalComplexLaurentIntegerChartRingHom N hN)) := by sorry
