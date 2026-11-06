-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectIntegralDifferentialTraceRegularity_functionFieldDifferentialTrace_directIntegral_smul_differential_mem_rationalAdic
-- name    : QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.functionFieldDifferentialTrace_directIntegral_smul_differential_mem_rationalAdic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:46:33.774109+00:00
-- url     : https://prove2.me/theorems/5035b581-8f6a-43f2-80ec-a0ac035ab834
-- title:
--   Direct Integral Differential Trace Regularity: function Field Differential Trace direct Integral smul differential mem rational Adic
-- statement:
--   Tracing `b dt` for direct integral `b,t` gives a differential regular at
--   every finite normalized rational place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralDifferentialTraceRegularity.lean#L209-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralDifferentialTraceRegularity.lean#L209-L220

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialTraceRegularity
set_option autoImplicit false
open scoped Polynomial RatFunc nonZeroDivisors
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity
open QEC.Coding.AlgebraicGeometry
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.integralDifferentialTraceRegularity_constantAlgebra
attribute [local instance] integralDifferentialTraceRegularity_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.integralDifferentialTraceRegularity_scalarTower
attribute [local instance] integralDifferentialTraceRegularity_scalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity._p2m_local_instance_828a280e13_54
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity._p2m_local_instance_828a280e13_58
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity._p2m_local_instance_828a280e13_61

theorem QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.functionFieldDifferentialTrace_directIntegral_smul_differential_mem_rationalAdic
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) (b t : B k F) :
    functionFieldDifferentialTrace (k := k) (F := F)
        ((algebraMap (B k F) F b) •
          differential k F (algebraMap (B k F) F t)) ∈
      Differential.localDifferentialLattice (GlobalPlace.rationalAdic p) := by sorry
