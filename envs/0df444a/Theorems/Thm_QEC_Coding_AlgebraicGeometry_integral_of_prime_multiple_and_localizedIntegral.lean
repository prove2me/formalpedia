-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_integral_of_prime_multiple_and_localizedIntegral
-- name    : QEC.Coding.AlgebraicGeometry.integral_of_prime_multiple_and_localizedIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:26:25.405658+00:00
-- url     : https://prove2.me/theorems/e0dc4e33-4971-4b28-a461-62b5fea52f2d
-- title:
--   Algebraic Geometry: integral of prime multiple and localized Integral
-- statement:
--   The Algebraic Geometry construction uses the integral of prime multiple and localized Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFiberDescent.lean#L48-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFiberDescent.lean#L48-L100

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Prime.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.integral_of_prime_multiple_and_localizedIntegral
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (P : Ideal R) [P.IsPrime] (J K : Type*) [Field J] [Field K]
    [Algebra R J] [IsFractionRing R J]
    [Algebra (Localization.AtPrime P) J]
    [IsScalarTower R (Localization.AtPrime P) J]
    [IsFractionRing (Localization.AtPrime P) J]
    [Algebra R K] [Algebra (Localization.AtPrime P) K] [Algebra J K]
    [IsScalarTower R J K] [IsScalarTower (Localization.AtPrime P) J K]
    [IsScalarTower R (Localization.AtPrime P) K]
    [FaithfulSMul R K] [FaithfulSMul (Localization.AtPrime P) K]
    [IsIntegrallyClosed (Localization.AtPrime P)]
    (a : R) (hP : P = Ideal.span {a}) (ha : Prime a) (y : K)
    (hR : IsIntegral R (algebraMap R K a*y))
    (hG : IsIntegral (Localization.AtPrime P) y) : IsIntegral R y := by sorry
