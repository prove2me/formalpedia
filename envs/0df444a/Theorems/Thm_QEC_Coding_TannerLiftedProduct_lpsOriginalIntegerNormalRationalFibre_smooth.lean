-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalRationalFibre_smooth
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalRationalFibre_smooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:22:33.133296+00:00
-- url     : https://prove2.me/theorems/6ee4f852-8e25-4b8f-95ad-414d3aff9903
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Rational Fibre smooth
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Rational Fibre smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L259-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCharacteristicZeroSmooth.lean#L259-L284

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
open CategoryTheory.Limits
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalRationalFibre_smooth
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    Smooth (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (lpsOriginalIntegerNormalGluedToSpecZ N hpos)) := by sorry
