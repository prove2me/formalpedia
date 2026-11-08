-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalLaurentBaseChangeIso_complexProjection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalLaurentBaseChangeIso_complexProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:13:55.560725+00:00
-- url     : https://prove2.me/theorems/51037afa-479c-45e8-af60-2f5ee801865d
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Laurent Base Change Iso complex Projection
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Laurent Base Change Iso complex Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L388-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L388-L394

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalLaurentBaseChangeIso_complexProjection
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalComplexNormalLaurentBaseChangeIso N hN).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (lpsOriginalComplexLaurentConstantRingHom N hN)) := by sorry
