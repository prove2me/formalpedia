-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityChart_smooth
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChart_smooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:18:48.403957+00:00
-- url     : https://prove2.me/theorems/5e5ce8a2-4c27-4c6b-bddf-84ef0d42f63c
-- title:
--   Tanner Lifted Product: lps Original Infinity Chart smooth
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Infinity Chart smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L65-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L65-L75

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCharacteristicZeroSmooth
set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChart_smooth (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    letI : Algebra ℂ (lpsOriginalComplexNormalInfinityChart N hpos) :=
      (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
    Algebra.Smooth ℂ (lpsOriginalComplexNormalInfinityChart N hpos) := by sorry
