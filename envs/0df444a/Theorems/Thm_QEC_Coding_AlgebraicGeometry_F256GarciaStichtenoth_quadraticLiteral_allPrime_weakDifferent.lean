-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_allPrime_weakDifferent
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_allPrime_weakDifferent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:55:01.899209+00:00
-- url     : https://prove2.me/theorems/7ffd7f52-f590-4d77-b39f-169258023afd
-- title:
--   F256 Garcia Stichtenoth: quadratic Literal all Prime weak Different
-- statement:
--   Every upper prime of a literal quadratic Artin--Schreier extension with
--   a normalized simple-pole or regular parameter has weak different exponent.
--   The quantifier is over supplied upper primes, not a selected extension of a
--   place. The only generator hypotheses are its equation and field generation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticDifferent.lean#L150-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticDifferent.lean#L150-L210

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticLocalModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K L : Type*} [_root_.Field K] [_root_.Field L]
  [Algebra F256 K] [Algebra K L]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_allPrime_weakDifferent
    [Algebra F256 L] [Algebra.IsSeparable K L]
    (P : GlobalPlace F256 K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure P.valuationRing L))
    [H.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.valuationRing)]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a) :
    multiplicity H.asIdeal
        (differentIdeal P.valuationRing (integralClosure P.valuationRing L)) =
      2 * ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' H.asIdeal - 1) := by sorry
