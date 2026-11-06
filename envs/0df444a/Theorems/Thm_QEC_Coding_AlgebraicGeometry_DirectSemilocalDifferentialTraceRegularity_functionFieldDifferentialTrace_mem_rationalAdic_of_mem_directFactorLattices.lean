-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalDifferentialTraceRegularity_functionFieldDifferentialTrace_mem_rationalAdic_of_mem_directFactorLattices
-- name    : QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity.functionFieldDifferentialTrace_mem_rationalAdic_of_mem_directFactorLattices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:44:51.833541+00:00
-- url     : https://prove2.me/theorems/5aff5f81-2f38-4c19-87f9-0f435425108b
-- title:
--   Direct Semilocal Differential Trace Regularity: function Field Differential Trace mem rational Adic of mem direct Factor Lattices
-- statement:
--   If a differential is regular at every actual upper factor over a direct
--   base prime, then its field trace is regular at that rational place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalDifferentialTraceRegularity.lean#L152-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalDifferentialTraceRegularity.lean#L152-L293

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialTraceRegularity
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalUniformizer
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalDifferentialTraceRegularity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
open QEC.Coding.AlgebraicGeometry
open FunctionFieldDifferential
open DirectIntegralDifferentialTraceRegularity
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity.semilocalDifferentialTraceRegularity_Algebra_1
attribute [local instance] semilocalDifferentialTraceRegularity_Algebra_1
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity.semilocalDifferentialTraceRegularity_ScalarTower_1
attribute [local instance] semilocalDifferentialTraceRegularity_ScalarTower_1
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity._p2m_local_instance_e20b542250_58
open DirectIntegralDifferentialResidue

theorem QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity.functionFieldDifferentialTrace_mem_rationalAdic_of_mem_directFactorLattices
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (omega : Differential k F)
    (homega : ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      omega ∈ Differential.localDifferentialLattice
        (AffinePlace.globalPlace k F (directFactorPlace k F p P))) :
    functionFieldDifferentialTrace (k := k) (F := F) omega ∈
      Differential.localDifferentialLattice (GlobalPlace.rationalAdic p) := by sorry
