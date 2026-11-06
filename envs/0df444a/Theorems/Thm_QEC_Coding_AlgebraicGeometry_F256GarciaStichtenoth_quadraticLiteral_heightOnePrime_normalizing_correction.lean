-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_heightOnePrime_normalizing_correction
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_heightOnePrime_normalizing_correction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:07:22.587178+00:00
-- url     : https://prove2.me/theorems/30ed0cec-5262-4f40-b904-4eba5e6f341c
-- title:
--   F256 Garcia Stichtenoth: quadratic Literal height One Prime normalizing correction
-- statement:
--   A literal quadratic insertion preserves normalized representatives for
--   every normalized lower parameter at a fixed global upper prime. No selected
--   place, local different formula, or order compatibility is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticGlobalNormalization.lean#L21-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticGlobalNormalization.lean#L21-L67

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticNormalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalNormalization
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_heightOnePrime_normalizing_correction
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    [IsDedekindDomain (integralClosure B L)]
    [IsFractionRing (integralClosure B L) L]
    [Module.IsTorsionFree B (integralClosure B L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    [Finite (heightOnePlace (k := F256) (K := K) H).residueField]
    (J : IsDedekindDomain.HeightOneSpectrum (integralClosure B L))
    [J.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a)
    (b : K)
    (hb : (heightOnePlace (k := F256) (K := K) H).order b = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order b) :
    ∃ c : L,
      (c = 0 ∨ (heightOnePlace (k := F256) (K := L) J).order c = -1) ∧
      ((heightOnePlace (k := F256) (K := L) J).order (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ (heightOnePlace (k := F256) (K := L) J).order (algebraMap K L b + c ^ 2 + c)) := by sorry
