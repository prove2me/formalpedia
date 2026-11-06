-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_transportedIntegralClosurePrime_order_predicate
-- name    : QEC.Coding.AlgebraicGeometry.transportedIntegralClosurePrime_order_predicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:49:56.146238+00:00
-- url     : https://prove2.me/theorems/9d5e298e-8a45-4293-ab3b-5465b5279041
-- title:
--   Algebraic Geometry: transported Integral Closure Prime order predicate
-- statement:
--   A property of the normalized upper order descends from localization to
--   the same supplied global prime. This transports actual parameter corrections
--   as elements of the unchanged fraction field, not just different exponents.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/PlaceLocalization.lean#L193-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/PlaceLocalization.lean#L193-L270

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_LocalizedPrime
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.transportedIntegralClosurePrime_order_predicate
    {k : Type*} [_root_.Field k] [Finite k]
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra k K] [Algebra k L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [FaithfulSMul P.valuationRing L]
    [IsDedekindDomain (integralClosure B L)]
    [IsFractionRing (integralClosure B L) L]
    [Module.IsTorsionFree B (integralClosure B L)]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (hvaluationRing : H.valuationSubringAtPrime K = P.valuationRing)
    (J : IsDedekindDomain.HeightOneSpectrum (integralClosure B L))
    [J.asIdeal.LiesOver H.asIdeal]
    (Φ : (L → ℤ) → Prop)
    (hlocal : ∀ R : IsDedekindDomain.HeightOneSpectrum (integralClosure P.valuationRing L),
      R.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) →
        Φ (heightOnePlace (k := k) (K := L) R).order) :
    Φ (heightOnePlace (k := k) (K := L) J).order := by sorry
