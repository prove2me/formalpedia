-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerInfinityChart_rationalSmooth
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerInfinityChart_rationalSmooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:21:09.898196+00:00
-- url     : https://prove2.me/theorems/a434c75f-ebe3-42ed-8a87-bbaf7cf647d4
-- title:
--   Tanner Lifted Product: lps Original Integer Infinity Chart rational Smooth
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Infinity Chart rational Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L161-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L161-L194

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCharacteristicZeroSmooth
set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerInfinityChart_rationalSmooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI : Algebra ℤ (lpsOriginalIntegerNormalInfinityChart N hpos) :=
      Ring.toIntAlgebra _
    letI : SMul ℤ (lpsOriginalIntegerNormalInfinityChart N hpos) := Algebra.toSMul
    letI : Module ℤ (lpsOriginalIntegerNormalInfinityChart N hpos) := Algebra.toModule
    Algebra.Smooth ℚ (ℚ ⊗[ℤ] lpsOriginalIntegerNormalInfinityChart N hpos) := by sorry
