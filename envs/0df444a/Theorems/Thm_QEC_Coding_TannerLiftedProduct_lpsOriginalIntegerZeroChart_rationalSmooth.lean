-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerZeroChart_rationalSmooth
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerZeroChart_rationalSmooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:19:31.552133+00:00
-- url     : https://prove2.me/theorems/4a90d89d-a893-42a3-9c4d-6f158da88e77
-- title:
--   Tanner Lifted Product: lps Original Integer Zero Chart rational Smooth
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Zero Chart rational Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L130-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L130-L159

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerZeroChart_rationalSmooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI : Algebra ℤ (lpsOriginalIntegerNormalZeroChart N hpos) :=
      Ring.toIntAlgebra _
    letI : SMul ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Algebra.toSMul
    letI : Module ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Algebra.toModule
    Algebra.Smooth ℚ (ℚ ⊗[ℤ] lpsOriginalIntegerNormalZeroChart N hpos) := by sorry
