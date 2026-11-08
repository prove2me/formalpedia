-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicValuationRing_formallySmooth
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicValuationRing_formallySmooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:25:11.544197+00:00
-- url     : https://prove2.me/theorems/a9706512-6890-4ef7-9e84-9510cd46db76
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Valuation Ring formally Smooth
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Meromorphic Valuation Ring formally Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L28-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L28-L46

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
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicValuationRing_formallySmooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
    (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    let V := Valuation.valuationSubring
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
    letI : Algebra ℂ V :=
      (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
    Algebra.FormallySmooth ℂ V := by sorry
