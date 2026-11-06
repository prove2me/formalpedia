-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorPrimaryTrace_primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace.primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:43:09.266224+00:00
-- url     : https://prove2.me/theorems/8319e3d3-fa77-4a9e-b620-721b98044b04
-- title:
--   Direct Factor Primary Trace: primary Torsion Trace direct Factor Quotient Mul eq quotient Trace
-- statement:
--   On one actual upper factor quotient, positive-depth primary trace of
--   multiplication is the ordinary quotient-field multiplication trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorPrimaryTrace.lean#L80-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorPrimaryTrace.lean#L80-L113

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

theorem QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace.primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    primaryTorsionTrace p.asIdeal
        (Algebra.lmul (R k) (B k F ⧸ (P : Ideal (B k F)))
          (Ideal.Quotient.mk (P : Ideal (B k F)) b)) depth =
      Algebra.trace (R k ⧸ p.asIdeal)
        (B k F ⧸ (P : Ideal (B k F)))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by sorry
