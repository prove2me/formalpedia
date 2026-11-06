-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_integralModel_normalizing_correction
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_integralModel_normalizing_correction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:07:25.516199+00:00
-- url     : https://prove2.me/theorems/be329e8b-08e7-462b-962e-5ed65dcc035f
-- title:
--   F256 Garcia Stichtenoth: quadratic Literal integral Model normalizing correction
-- statement:
--   The same correction on any actual upper integral-closure carrier,
--   including an absolute integral model over the fixed initial base.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticGlobalNormalization.lean#L71-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticGlobalNormalization.lean#L71-L123

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticNormalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalNormalization
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_integralModel_normalizing_correction
    (A B C K L : Type*) [CommRing A] [CommRing B] [CommRing C]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsFractionRing C L] [IsScalarTower B C L]
    [IsIntegralClosure C B L] [Module.IsTorsionFree B C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    [Finite (heightOnePlace (k := F256) (K := K) H).residueField]
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a)
    (b : K)
    (hb : (heightOnePlace (k := F256) (K := K) H).order b = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order b) :
    ∃ c : L,
      (c = 0 ∨ (heightOnePlace (k := F256) (K := L) Q).order c = -1) ∧
      ((heightOnePlace (k := F256) (K := L) Q).order (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ (heightOnePlace (k := F256) (K := L) Q).order (algebraMap K L b + c ^ 2 + c)) := by sorry
