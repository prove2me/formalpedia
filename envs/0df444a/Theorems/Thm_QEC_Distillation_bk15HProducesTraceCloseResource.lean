-- Prove2me | Theorems.Thm_QEC_Distillation_bk15HProducesTraceCloseResource
-- name    : QEC.Distillation.bk15HProducesTraceCloseResource
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T21:32:03.801184+00:00
-- url     : https://prove2.me/theorems/a53e8796-a434-41be-9cb6-a62e229dd0ff
-- title:
--   Distillation: bk15 HProduces Trace Close Resource
-- statement:
--   Raw trace-norm strengthening of
--   `BK15.Threshold.bk15HfidelityDistillation`.  The strict branch exposes the
--   actual finite semantic run and returns its literal inverse-frame H density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L662-L797
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L662-L797

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
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

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

theorem QEC.Distillation.bk15HProducesTraceCloseResource
    (rho : DensityOperator QubitSpace)
    (hfidelity : BK15.Threshold.FStar < hFidelity rho)
    (eta : Real) (heta : 0 < eta) :
    ∃ rounds : Nat,
      traceNorm
        ((BK15.Threshold.bk15AcceptedRunHOutput rho rounds).toOperator -
          hMagicState.toOperator) < eta ∧
        (BK15.Threshold.bk15HInputError rho = 0 ∨
          ∃ (hpositive : 0 < BK15.Threshold.bk15HInputError rho)
            (hthreshold : BK15.Threshold.bk15HInputError rho <
              BK15.Threshold.epsilonStar) (depth : Nat),
            rounds = depth + 1 ∧
            BK15.Threshold.BK15SemanticSchedule.leafCount
                (BK15.Threshold.bk15CompleteSemanticSchedule
                  rho hpositive hthreshold (depth + 1)) =
              15 ^ (depth + 1) ∧
            BK15.Threshold.BK15SemanticSchedule.rootInput
                (BK15.Threshold.bk15CompleteSemanticSchedule
                  rho hpositive hthreshold (depth + 1)) =
              (BK15.Protocol.bk15Run
                (BK15.Threshold.bk15IterationEpsilon
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth)
                (BK15.Threshold.bk15Iteration_pos_and_lt_epsilonStar
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth).1).noisyInput ∧
            BK15.Threshold.BK15SemanticSchedule.preparedInput
                (BK15.Threshold.bk15CompleteSemanticSchedule
                  rho hpositive hthreshold (depth + 1)) =
              (BK15.Protocol.bk15Run
                (BK15.Threshold.bk15IterationEpsilon
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth)
                (BK15.Threshold.bk15Iteration_pos_and_lt_epsilonStar
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
                ((BK15.Protocol.bk15Run
                  (BK15.Threshold.bk15IterationEpsilon
                    (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth)
                  (BK15.Threshold.bk15Iteration_pos_and_lt_epsilonStar
                    (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) ∧
            BK15.Threshold.BK15SemanticSchedule.rootOutput
                (BK15.Threshold.bk15CompleteSemanticSchedule
                  rho hpositive hthreshold (depth + 1)) =
              (BK15.Protocol.bk15Run
                (BK15.Threshold.bk15IterationEpsilon
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth)
                (BK15.Threshold.bk15Iteration_pos_and_lt_epsilonStar
                  (BK15.Threshold.bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput ∧
            BK15.Threshold.bk15AcceptedRunHOutput rho (depth + 1) =
              BK15.NoisyInput.sourceA0Transport.symm.conjDensity
                (BK15.Threshold.BK15SemanticSchedule.rootOutput
                  (BK15.Threshold.bk15CompleteSemanticSchedule
                    rho hpositive hthreshold (depth + 1)))) := by sorry
