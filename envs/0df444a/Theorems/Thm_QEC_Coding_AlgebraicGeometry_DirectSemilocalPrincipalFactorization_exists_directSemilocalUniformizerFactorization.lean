-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalPrincipalFactorization_exists_directSemilocalUniformizerFactorization
-- name    : QEC.Coding.AlgebraicGeometry.DirectSemilocalPrincipalFactorization.exists_directSemilocalUniformizerFactorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:48:06.977038+00:00
-- url     : https://prove2.me/theorems/7552dcda-1648-4974-9ad9-75afe4d5f8ad
-- title:
--   Direct Semilocal Principal Factorization: exists direct Semilocal Uniformizer Factorization
-- statement:
--   There is one simultaneous direct uniformizer whose principal ideal is the
--   product of all actual upper factors times a complement coprime to the full
--   extended base prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalPrincipalFactorization.lean#L51-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalPrincipalFactorization.lean#L51-L136

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalUniformizer
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalPrincipalFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalPrincipalFactorization
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
open DirectIntegralDifferentialResidue
open DirectFactorSemilocalLogarithmicResidue
open DirectSemilocalUniformizer
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalPrincipalFactorization._p2m_local_instance_698d2271dc_39
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalPrincipalFactorization._p2m_local_instance_698d2271dc_44

theorem QEC.Coding.AlgebraicGeometry.DirectSemilocalPrincipalFactorization.exists_directSemilocalUniformizerFactorization
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    ∃ t : B k F, t ≠ 0 ∧ ∃ J : Ideal (B k F),
      Ideal.span ({t} : Set (B k F)) =
          (∏ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
              (P : Ideal (B k F))) * J ∧
        IsCoprime
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J ∧
        ∀ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          GlobalPlace.order
              (AffinePlace.globalPlace k F (directFactorPlace k F p P))
              (algebraMap (B k F) F t) = 1 := by sorry
