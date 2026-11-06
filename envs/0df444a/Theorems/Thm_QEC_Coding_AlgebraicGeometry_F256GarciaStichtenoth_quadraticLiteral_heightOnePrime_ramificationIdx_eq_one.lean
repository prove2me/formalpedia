-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_heightOnePrime_ramificationIdx_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_heightOnePrime_ramificationIdx_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:00:16.587388+00:00
-- url     : https://prove2.me/theorems/d2b85ac2-e45b-4e55-9b0e-8d5efb429cf7
-- title:
--   F256 Garcia Stichtenoth: quadratic Literal height One Prime ramification Idx eq one
-- statement:
--   A regular parameter gives index one at the supplied prime of the
--   actual integral closure, even when the lower ring is not itself local.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticGlobalRegular.lean#L19-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticGlobalRegular.lean#L19-L56

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_heightOnePrime_ramificationIdx_eq_one
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.IsTorsionFree B L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (J : Ideal (integralClosure B L)) [J.IsPrime] [J.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : 0 ≤ (heightOnePlace (k := F256) (K := K) H).order a) :
    H.asIdeal.ramificationIdx' J = 1 := by sorry
