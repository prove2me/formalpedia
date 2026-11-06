-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_integralModel_ramificationIdx_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_integralModel_ramificationIdx_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:00:36.730386+00:00
-- url     : https://prove2.me/theorems/5dd19790-ac2b-4127-b4f7-2085bc374b38
-- title:
--   F256 Garcia Stichtenoth: quadratic Literal integral Model ramification Idx eq one
-- statement:
--   The regular calculation on any actual integral-closure carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticGlobalRegular.lean#L59-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticGlobalRegular.lean#L59-L94

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_integralModel_ramificationIdx_eq_one
    (A B C K L : Type*) [CommRing A] [CommRing B] [CommRing C]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsScalarTower B C L]
    [IsIntegralClosure C B L] [Module.IsTorsionFree B C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.IsTorsionFree B L]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : 0 ≤ (heightOnePlace (k := F256) (K := K) H).order a) :
    H.asIdeal.ramificationIdx' Q.asIdeal = 1 := by sorry
