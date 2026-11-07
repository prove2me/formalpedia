-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteDecodedTrace_normalized_residual_traceNorm_le
-- name    : QEC.Distillation.FiniteDecodedTrace.normalized_residual_traceNorm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:58:09.659562+00:00
-- url     : https://prove2.me/theorems/0867e3b8-b7c5-42ea-aca9-aa3caead0788
-- title:
--   Finite Decoded Trace: normalized residual trace Norm le
-- statement:
--   Scaling a residual by the inverse of a positive real success mass preserves
--   its trace estimate with the same explicit normalization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteDecodedTrace.lean#L55-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteDecodedTrace.lean#L55-L67

import Definitions.Def_QEC_Distillation_Core_FiniteCentering
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.FiniteDecodedTrace
open Semantics
open scoped BigOperators
universe u v

theorem QEC.Distillation.FiniteDecodedTrace.normalized_residual_traceNorm_le
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (success residualMass : ℝ) (residual : Operator H)
    (hsuccess : 0 < success)
    (hresidual : traceNorm residual ≤ 2 * residualMass) :
    traceNorm ((success : Complex)⁻¹ • residual) ≤ 2 * (residualMass / success) := by sorry
