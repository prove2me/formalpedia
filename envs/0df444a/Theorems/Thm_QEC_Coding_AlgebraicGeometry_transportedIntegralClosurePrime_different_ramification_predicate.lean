-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_transportedIntegralClosurePrime_different_ramification_predicate
-- name    : QEC.Coding.AlgebraicGeometry.transportedIntegralClosurePrime_different_ramification_predicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:23.602068+00:00
-- url     : https://prove2.me/theorems/818ba354-6006-48fc-a44c-25d10ce9aefe
-- title:
--   Algebraic Geometry: transported Integral Closure Prime different ramification predicate
-- statement:
--   A property of the actual different exponent and ramification index
--   descends from localization to the same supplied global prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/PlaceLocalization.lean#L72-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/PlaceLocalization.lean#L72-L158

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_LocalizedPrime
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.transportedIntegralClosurePrime_different_ramification_predicate
    {k : Type*} [_root_.Field k] [Finite k]
    (A B K L : Type*)
    [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B]
    [Algebra k K]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L]
    [IsScalarTower P.valuationRing K L]
    [FaithfulSMul P.valuationRing L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing
      (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (hvaluationRing : H.valuationSubringAtPrime K = P.valuationRing)
    (J : Ideal (integralClosure B L))
    [J.IsPrime] [J.LiesOver H.asIdeal]
    (Φ : ℕ → ℕ → Prop)
    (hlocal : ∀ R : Ideal (integralClosure P.valuationRing L),
      R.IsPrime →
      R.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) →
      Φ (multiplicity R
          (differentIdeal P.valuationRing
            (integralClosure P.valuationRing L)))
        ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' R)) :
    Φ (multiplicity J (differentIdeal B (integralClosure B L)))
      (H.asIdeal.ramificationIdx' J) := by sorry
