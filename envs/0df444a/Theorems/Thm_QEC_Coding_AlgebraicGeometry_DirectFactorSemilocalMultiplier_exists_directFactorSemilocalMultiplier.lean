-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalMultiplier_exists_directFactorSemilocalMultiplier
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier.exists_directFactorSemilocalMultiplier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:56.71032+00:00
-- url     : https://prove2.me/theorems/73a4168e-d200-40d5-bc6d-0a9784a6d5ee
-- title:
--   Direct Factor Semilocal Multiplier: exists direct Factor Semilocal Multiplier
-- statement:
--   Every chosen direct upper factor has an integral principal multiplier
--   whose remaining ideal factor is coprime to the extended base prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalMultiplier.lean#L47-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalMultiplier.lean#L47-L88

import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier._p2m_local_instance_e0603924bb_41

theorem QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier.exists_directFactorSemilocalMultiplier
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    ∃ t : B k F, t ≠ 0 ∧ ∃ J : Ideal (B k F),
      Ideal.span ({t} : Set (B k F)) = (P : Ideal (B k F)) * J ∧
        IsCoprime
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J := by sorry
