-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroChart_smooth
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChart_smooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:21:11.046219+00:00
-- url     : https://prove2.me/theorems/6d3f53bb-d5ce-49b9-9419-4e65fe5fe0ea
-- title:
--   Tanner Lifted Product: lps Original Zero Chart smooth
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Zero Chart smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L53-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L53-L63

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChart_smooth (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    letI : Algebra ℂ (lpsOriginalComplexNormalZeroChart N hpos) :=
      (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
    Algebra.Smooth ℂ (lpsOriginalComplexNormalZeroChart N hpos) := by sorry
