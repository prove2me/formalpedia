-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalCokernelTraceSum_exists_directSemilocalUniformizer_primaryTrace_eq_sum_factorResidueTrace
-- name    : QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum.exists_directSemilocalUniformizer_primaryTrace_eq_sum_factorResidueTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:49:10.293191+00:00
-- url     : https://prove2.me/theorems/a2514851-7588-411e-83f4-9250e1caf4f5
-- title:
--   Direct Semilocal Cokernel Trace Sum: exists direct Semilocal Uniformizer primary Trace eq sum factor Residue Trace
-- statement:
--   One simultaneous direct uniformizer realizes the grouped factor-residue
--   sum as a principal-cokernel primary trace and has order one at every upper
--   place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalCokernelTraceSum.lean#L187-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalCokernelTraceSum.lean#L187-L208

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalPrincipalFactorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CoprimeQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalCokernelTraceSum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum._p2m_local_instance_fa03a56197_45
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum._p2m_local_instance_fa03a56197_50

theorem QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum.exists_directSemilocalUniformizer_primaryTrace_eq_sum_factorResidueTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    ∃ t : B k F, t ≠ 0 ∧
      (∀ P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        GlobalPlace.order
            (AffinePlace.globalPlace k F
              (DirectIntegralDifferentialResidue.directFactorPlace k F p P))
            (algebraMap (B k F) F t) = 1) ∧
      Ideal.Factors.quotientResidueEquiv p.asIdeal
          (primaryTorsionTrace p.asIdeal
            (principalCokernelMul (R := R k) t b) depth) =
        ∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          Ideal.Factors.factorResidueTrace p.asIdeal P b := by sorry
