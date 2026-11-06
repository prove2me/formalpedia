-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalDenominator_exists_directSemilocal_integral_multiple
-- name    : QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator.exists_directSemilocal_integral_multiple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:38:38.394942+00:00
-- url     : https://prove2.me/theorems/3a4a6351-98bf-4db9-8e74-f6e0e3bb0c82
-- title:
--   Direct Semilocal Denominator: exists direct Semilocal integral multiple
-- statement:
--   If `x` is regular at every actual upper factor over a direct base prime,
--   then one polynomial which is nonzero modulo the base prime sends `x` into the
--   direct integral closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalDenominator.lean#L50-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalDenominator.lean#L50-L150

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalDenominator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator
open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator._p2m_local_instance_ebdac87835_36
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator._p2m_local_instance_ebdac87835_41
open DirectIntegralDifferentialResidue

theorem QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator.exists_directSemilocal_integral_multiple
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) (x : F)
    (hx : ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      GlobalPlace.RegularAt
        (AffinePlace.globalPlace k F (directFactorPlace k F p P)) x) :
    ∃ a : R k, a ∉ p.asIdeal ∧ ∃ b : B k F,
      algebraMap (B k F) F b = algebraMap (R k) F a * x := by sorry
