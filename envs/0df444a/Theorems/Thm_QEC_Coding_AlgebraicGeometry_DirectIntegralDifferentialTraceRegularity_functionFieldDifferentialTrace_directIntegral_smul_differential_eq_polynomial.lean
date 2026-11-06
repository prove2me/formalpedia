-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectIntegralDifferentialTraceRegularity_functionFieldDifferentialTrace_directIntegral_smul_differential_eq_polynomial
-- name    : QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.functionFieldDifferentialTrace_directIntegral_smul_differential_eq_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:43:36.20121+00:00
-- url     : https://prove2.me/theorems/5a50468c-1928-4002-9f6d-988eb6f0409e
-- title:
--   Direct Integral Differential Trace Regularity: function Field Differential Trace direct Integral smul differential eq polynomial
-- statement:
--   The differential trace of `b dt` for direct integral `b,t` is the image
--   of an actual polynomial times the rational differential generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralDifferentialTraceRegularity.lean#L142-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralDifferentialTraceRegularity.lean#L142-L205

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

theorem QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.functionFieldDifferentialTrace_directIntegral_smul_differential_eq_polynomial
    (b t : B k F) :
    functionFieldDifferentialTrace (k := k) (F := F)
        ((algebraMap (B k F) F b) •
          differential k F (algebraMap (B k F) F t)) =
      algebraMap (R k) (RatFunc k)
          (directIntegralDifferentialTracePolynomial k F b t) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by sorry
