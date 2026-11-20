-- Prove2me | Theorems.Thm_QEC_Distillation_tRejectedDataRaw_discardsFullPair
-- name    : QEC.Distillation.tRejectedDataRaw_discardsFullPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T21:31:10.236055+00:00
-- url     : https://prove2.me/theorems/2c95866e-1d4a-44c2-b6b1-2fcda0c539ff
-- title:
--   Distillation: t Rejected Data Raw discards Full Pair
-- statement:
--   The rejected source-T branch is discarded as a complete two-qubit right
--   factor.  This local trace-pairing proof rules out a one-qubit or normalized
--   postselection surrogate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L1002-L1029
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L1002-L1029

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

theorem QEC.Distillation.tRejectedDataRaw_discardsFullPair (data : Operator QubitSpace)
    (t : DensityOperator QubitSpace) :
    tRejectedDataRaw data t =
      (LinearMap.trace Complex TwoQubit.TwoQubitSpace (tPairBranchRaw t false)) • data := by sorry
