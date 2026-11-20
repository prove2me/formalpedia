-- Prove2me | Theorems.Thm_QEC_Distillation_traceNorm_tensor_right_resource_le
-- name    : QEC.Distillation.traceNorm_tensor_right_resource_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T21:31:36.933525+00:00
-- url     : https://prove2.me/theorems/ac317c64-b398-47c4-944b-964def8fd988
-- title:
--   Distillation: trace Norm tensor right resource le
-- statement:
--   Tensoring on a fixed data density is a concrete CPTP preparation followed
--   by a factor swap, and hence cannot increase the trace norm of a self-adjoint
--   resource difference.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L1115-L1156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L1115-L1156

import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Distillation_MagicStateThreshold_Universality
set_option autoImplicit false
noncomputable section
universe u v
open QEC
open QEC.Distillation
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open GeneratedUniversality
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators Matrix.Norms.Elementwise
open AdaptiveIdealClifford PhaseInjection

theorem QEC.Distillation.traceNorm_tensor_right_resource_le
    (data resource ideal : DensityOperator QubitSpace) :
    traceNorm
      (TensorProduct.map data.toOperator resource.toOperator -
        TensorProduct.map data.toOperator ideal.toOperator) ≤
      traceNorm (resource.toOperator - ideal.toOperator) := by sorry
