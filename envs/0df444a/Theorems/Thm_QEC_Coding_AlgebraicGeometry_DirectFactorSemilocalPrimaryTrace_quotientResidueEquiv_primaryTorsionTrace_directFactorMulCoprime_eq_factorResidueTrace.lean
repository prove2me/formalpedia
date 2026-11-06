-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalPrimaryTrace_quotientResidueEquiv_primaryTorsionTrace_directFactorMulCoprime_eq_factorResidueTrace
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace.quotientResidueEquiv_primaryTorsionTrace_directFactorMulCoprime_eq_factorResidueTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:16:53.549197+00:00
-- url     : https://prove2.me/theorems/9d678ad6-9f9b-4200-930e-d8614e6a6a0f
-- title:
--   Direct Factor Semilocal Primary Trace: quotient Residue Equiv primary Torsion Trace direct Factor Mul Coprime eq factor Residue Trace
-- statement:
--   Canonical base-residue transport sends the semilocal primary trace to
--   the established residue trace of the chosen upper factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalPrimaryTrace.lean#L89-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalPrimaryTrace.lean#L89-L105

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CoprimeQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalPrimaryTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace
open scoped Polynomial RatFunc nonZeroDivisors
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
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace._p2m_local_instance_de14ef7384_45
open DirectFactorPrimaryTrace

theorem QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace.quotientResidueEquiv_primaryTorsionTrace_directFactorMulCoprime_eq_factorResidueTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    Ideal.Factors.quotientResidueEquiv p.asIdeal
        (primaryTorsionTrace p.asIdeal
          (Algebra.lmul (R k) (B k F ⧸ ((P : Ideal (B k F)) * J))
            (Ideal.Quotient.mk ((P : Ideal (B k F)) * J) b)) depth) =
      Ideal.Factors.factorResidueTrace p.asIdeal P b := by sorry
