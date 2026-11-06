-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticCompositumCell_normalized_weakDifferent
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticCompositumCell_normalized_weakDifferent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:08:50.217794+00:00
-- url     : https://prove2.me/theorems/cb32db63-52fd-498d-9d71-d0bc7439d5ec
-- title:
--   F256 Garcia Stichtenoth: quadratic Compositum Cell normalized weak Different
-- statement:
--   One genuine quadratic upper edge of the compositum square. The returned
--   parameter and generator can be used in the next square: their normalization,
--   literal equation, full generation, and actual different are all proved.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticCompositumCell.lean#L113-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticCompositumCell.lean#L113-L145

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalNormalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable (A B C D K L E : Type*)
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [_root_.Field K] [_root_.Field L] [_root_.Field E]
    [IsDomain A] [IsLocalRing A]
    [IsDedekindDomain B] [IsDedekindDomain C] [IsDedekindDomain D]
    [Algebra F256 K] [Algebra F256 L] [Algebra F256 E]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra A C] [Algebra.IsIntegral A C] [Module.IsTorsionFree A C]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsFractionRing C L] [IsScalarTower B C L]
    [IsIntegralClosure C B L] [Module.IsTorsionFree B C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    [Algebra C E] [IsScalarTower C L E]
    [Algebra C D] [Algebra D E] [IsScalarTower C D E]
    [IsIntegralClosure D C E] [Module.IsTorsionFree C D]
    [FiniteDimensional L E] [Algebra.IsSeparable L E]
    [Module.IsTorsionFree C E]
include A

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticCompositumCell_normalized_weakDifferent
    (H : IsDedekindDomain.HeightOneSpectrum B)
    [Finite (heightOnePlace (k := F256) (K := K) H).residueField]
    (P : IsDedekindDomain.HeightOneSpectrum C) [P.asIdeal.LiesOver H.asIdeal]
    (Q : IsDedekindDomain.HeightOneSpectrum D) [Q.asIdeal.LiesOver P.asIdeal]
    (a b : K) (y : L) (z : E)
    (hy : y ^ 2 + y = algebraMap K L a)
    (hz : z ^ 2 + z = algebraMap K E b)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (hdegreeUpper : Module.finrank L E = 2) (hgenUpper : L⟮z⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a)
    (hb : (heightOnePlace (k := F256) (K := K) H).order b = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order b) :
    ∃ c : L,
      ((heightOnePlace (k := F256) (K := L) P).order
          (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ (heightOnePlace (k := F256) (K := L) P).order
          (algebraMap K L b + c ^ 2 + c)) ∧
      (z + algebraMap L E c) ^ 2 + (z + algebraMap L E c) =
        algebraMap L E (algebraMap K L b + c ^ 2 + c) ∧
      L⟮z + algebraMap L E c⟯ = ⊤ ∧
      multiplicity Q.asIdeal (differentIdeal C D) =
        2 * (P.asIdeal.ramificationIdx' Q.asIdeal - 1) := by sorry
