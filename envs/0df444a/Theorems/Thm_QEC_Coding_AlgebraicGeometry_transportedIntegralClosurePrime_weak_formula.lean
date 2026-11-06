-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_transportedIntegralClosurePrime_weak_formula
-- name    : QEC.Coding.AlgebraicGeometry.transportedIntegralClosurePrime_weak_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:34.060763+00:00
-- url     : https://prove2.me/theorems/b44ffa0a-195d-4c1a-ba2a-c03ab93ac0ea
-- title:
--   Algebraic Geometry: transported Integral Closure Prime weak formula
-- statement:
--   The weak-different specialization of the same localization transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/PlaceLocalization.lean#L161-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/PlaceLocalization.lean#L161-L187

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_LocalizedPrime
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.transportedIntegralClosurePrime_weak_formula
    {k : Type*} [_root_.Field k] [Finite k]
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra k K] [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.IsTorsionFree B L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [FaithfulSMul P.valuationRing L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (hvaluationRing : H.valuationSubringAtPrime K = P.valuationRing)
    (J : Ideal (integralClosure B L)) [J.IsPrime] [J.LiesOver H.asIdeal]
    (hlocal : ∀ R : Ideal (integralClosure P.valuationRing L),
      R.IsPrime → R.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) →
        multiplicity R (differentIdeal P.valuationRing (integralClosure P.valuationRing L)) =
          2 * ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' R - 1)) :
    multiplicity J (differentIdeal B (integralClosure B L)) =
      2 * (H.asIdeal.ramificationIdx' J - 1) := by sorry
