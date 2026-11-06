-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_localizedIntegralClosurePrime_ramificationIdx_and_multiplicity_eq
-- name    : QEC.Coding.AlgebraicGeometry.localizedIntegralClosurePrime_ramificationIdx_and_multiplicity_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:23:05.828613+00:00
-- url     : https://prove2.me/theorems/3159a695-6d53-4fdc-be0d-e28b7810b114
-- title:
--   Algebraic Geometry: localized Integral Closure Prime ramification Idx and multiplicity eq
-- statement:
--   Mapping an existing global upper prime into the localized integral
--   closure preserves its ramification index and different multiplicity.  This
--   is the direction needed by the all-prime normal-closure formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/LocalizedPrime.lean#L39-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/LocalizedPrime.lean#L39-L173

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Localization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalIntegralClosureFree
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_LocalizedPrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.localizedIntegralClosurePrime_ramificationIdx_and_multiplicity_eq
    (A B Bm K L : Type*)
    [CommRing A] [CommRing B] [CommRing Bm]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A]
    [IsDomain Bm] [IsLocalRing Bm]
    [IsDedekindDomain B] [IsDedekindDomain Bm]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B]
    [Algebra B Bm] [Module.IsTorsionFree B Bm]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra Bm K] [IsScalarTower B Bm K]
    [Algebra Bm L] [IsScalarTower B Bm L]
    [IsScalarTower Bm K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L] [Module.IsTorsionFree Bm L]
    (p : Ideal B) [p.IsPrime] (hp : p ≠ ⊥)
    [IsLocalization p.primeCompl Bm]
    (J : Ideal (integralClosure B L))
    [J.IsPrime] [J.LiesOver p] :
    letI : IsFractionRing Bm K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
        p.primeCompl Bm K
    letI : IsScalarTower B (integralClosure B L) L :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Bm (integralClosure Bm L) L :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Module.IsTorsionFree B (integralClosure B L) :=
      IsIntegralClosure.isTorsionFree B L
    letI : Module.IsTorsionFree Bm (integralClosure Bm L) :=
      IsIntegralClosure.isTorsionFree Bm L
    letI : Module.Finite B (integralClosure B L) :=
      IsIntegralClosure.finite B K L (integralClosure B L)
    letI : Module.Finite Bm (integralClosure Bm L) :=
      IsIntegralClosure.finite Bm K L (integralClosure Bm L)
    letI : IsDedekindDomain (integralClosure B L) :=
      integralClosure.isDedekindDomain B K L
    letI : IsDedekindDomain (integralClosure Bm L) :=
      integralClosure.isDedekindDomain Bm K L
    let R := Ideal.map (localizedIntegralClosureMap B Bm L) J
    R.IsPrime ∧
      R.LiesOver (IsLocalRing.maximalIdeal Bm) ∧
      (IsLocalRing.maximalIdeal Bm).ramificationIdx' R =
        p.ramificationIdx' J ∧
      multiplicity R (differentIdeal Bm (integralClosure Bm L)) =
        multiplicity J (differentIdeal B (integralClosure B L)) := by sorry
