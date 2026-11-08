-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGluedToSpecC_smooth
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGluedToSpecC_smooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:20:32.680765+00:00
-- url     : https://prove2.me/theorems/7d5a82ab-2535-4793-96fe-8d63a532a54b
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Glued To Spec C smooth
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Glued To Spec C smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L110-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L110-L124

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGluedToSpecC_smooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    Smooth (lpsOriginalComplexNormalGluedToSpecC N hpos) := by sorry
