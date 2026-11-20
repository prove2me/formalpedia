-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFractionCoordinate_not_prime_power
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFractionCoordinate_not_prime_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:26:28.415556+00:00
-- url     : https://prove2.me/theorems/7ad2939b-09ca-4d58-8d71-7760d9f1657e
-- title:
--   Tanner Lifted Product: lps Original Fraction Coordinate not prime power
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Fraction Coordinate not prime power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L394-L408
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L394-L408

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFractionCoordinate_not_prime_power
    (F : Type*) [Field F] (p : ℕ) (hp : p.Prime)
    (u : FractionRing (Polynomial F)) :
    u^p ≠ algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X := by sorry
