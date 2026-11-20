-- Prove2me | Theorems.Thm_QEC_Distillation_tActualRawTree_aggregate_traceNorm_le
-- name    : QEC.Distillation.tActualRawTree_aggregate_traceNorm_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T21:32:35.099543+00:00
-- url     : https://prove2.me/theorems/2a24c9ee-2b20-4cc2-8c5b-0064d3d1101b
-- title:
--   Distillation: t Actual Raw Tree aggregate trace Norm le
-- statement:
--   The actual unconditioned T retry aggregate changes by at most two source
--   resource trace distances for each bounded fresh-pair attempt at each of the
--   literal order-twelve phase sites.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L4984-L5003
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L4984-L5003

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

theorem QEC.Distillation.tActualRawTree_aggregate_traceNorm_le
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (blocks : Nat) (rho : DensityOperator QubitSpace) :
    traceNorm
      (rawAggregate (tActualRawTree t pairAttempts target blocks rho) -
        rawAggregate (tActualRawTree tMagicState pairAttempts target blocks rho)) ≤
      (2 * pairAttempts * 12 * blocks : Real) *
        traceNorm (t.toOperator - tMagicState.toOperator) := by sorry
