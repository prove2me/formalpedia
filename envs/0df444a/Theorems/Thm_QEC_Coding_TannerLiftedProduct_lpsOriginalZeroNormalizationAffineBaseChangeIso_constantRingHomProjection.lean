-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroNormalizationAffineBaseChangeIso_constantRingHomProjection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalZeroNormalizationAffineBaseChangeIso_constantRingHomProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:59:42.524682+00:00
-- url     : https://prove2.me/theorems/e8aae46c-7ed9-48ae-9d63-8c0ba5b52034
-- title:
--   Tanner Lifted Product: lps Original Zero Normalization Affine Base Change Iso constant Ring Hom Projection
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Zero Normalization Affine Base Change Iso constant Ring Hom Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L118-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean#L118-L122

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary001
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary002
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary013
local notation "ICL" => integralClosure (LaurentPolynomial ℂ) FC
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary016
local notation "IC0" => integralClosure (Polynomial ℂ) FC
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroComplexAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroIntegerAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroIntegerModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroSelfAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroSelfSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroSelfModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroIntegerSelfTower
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeLaurentSelfAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeLaurentSelfSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeLaurentSelfModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeLaurentIntegerSelfTower
attribute [local irreducible] lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalZeroNormalizationAffineBaseChangeIso_constantRingHomProjection :
    (lpsOriginalZeroNormalizationAffineBaseChangeIso N hN).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (lpsOriginalComplexZeroConstantRingHom N hN)) := by sorry
