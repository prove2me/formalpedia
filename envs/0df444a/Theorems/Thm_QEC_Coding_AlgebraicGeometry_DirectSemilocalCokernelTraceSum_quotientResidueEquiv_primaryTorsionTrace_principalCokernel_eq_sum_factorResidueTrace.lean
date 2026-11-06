-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalCokernelTraceSum_quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_sum_factorResidueTrace
-- name    : QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum.quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_sum_factorResidueTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:50:18.785719+00:00
-- url     : https://prove2.me/theorems/04028c88-17f9-42c0-aa3a-6ee5d5f33277
-- title:
--   Direct Semilocal Cokernel Trace Sum: quotient Residue Equiv primary Torsion Trace principal Cokernel eq sum factor Residue Trace
-- statement:
--   For a simultaneous principal factorization, canonical base-residue
--   transport turns the principal-cokernel primary trace into the sum of the
--   actual factor residue traces over the direct fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalCokernelTraceSum.lean#L111-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalCokernelTraceSum.lean#L111-L182

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

theorem QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum.quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_sum_factorResidueTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (∏ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          (P : Ideal (B k F))) * J)
    (depth : ℕ) (hdepth : 0 < depth) :
    Ideal.Factors.quotientResidueEquiv p.asIdeal
        (primaryTorsionTrace p.asIdeal
          (principalCokernelMul (R := R k) t b) depth) =
      ∑ P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        Ideal.Factors.factorResidueTrace p.asIdeal P b := by sorry
