-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorPrimaryTrace_quotientResidueEquiv_primaryTorsionTrace_directFactorQuotientMul_eq_factorResidueTrace
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace.quotientResidueEquiv_primaryTorsionTrace_directFactorQuotientMul_eq_factorResidueTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:17:01.841178+00:00
-- url     : https://prove2.me/theorems/0ea4d5a5-8eb0-4d8d-8f69-9f2e7340da8d
-- title:
--   Direct Factor Primary Trace: quotient Residue Equiv primary Torsion Trace direct Factor Quotient Mul eq factor Residue Trace
-- statement:
--   After canonical quotient-to-residue transport, the primary trace on one
--   upper factor quotient is its actual factor residue trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorPrimaryTrace.lean#L117-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorPrimaryTrace.lean#L117-L130

import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_AnnihilatedTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorPrimaryTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace
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
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace._p2m_local_instance_a98a1bf31e_44

theorem QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace.quotientResidueEquiv_primaryTorsionTrace_directFactorQuotientMul_eq_factorResidueTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    Ideal.Factors.quotientResidueEquiv p.asIdeal
        (primaryTorsionTrace p.asIdeal
          (Algebra.lmul (R k) (B k F ⧸ (P : Ideal (B k F)))
            (Ideal.Quotient.mk (P : Ideal (B k F)) b)) depth) =
      Ideal.Factors.factorResidueTrace p.asIdeal P b := by sorry
