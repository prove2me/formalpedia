-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_rootOutput_dephased_eq_iterationResource
-- name    : QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_rootOutput_dephased_eq_iterationResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:27:23.777909+00:00
-- url     : https://prove2.me/theorems/d49a3725-fd69-49fc-afe5-c63856188d27
-- title:
--   Threshold: bk15 Semantic Schedule root Output dephased eq iteration Resource
-- statement:
--   Dephasing the root of a complete semantic schedule gives the exact
--   diagonal A resource at the corresponding recurrence depth.  The base case is
--   the literal H-to-A transport; every successor uses the actual accepted layer
--   handoff.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L936-L955
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L936-L955

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic

theorem QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_rootOutput_dephased_eq_iterationResource
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (rounds : Nat) :
    aBasisDephasing.mapDensity
        (BK15SemanticSchedule.rootOutput
          (bk15CompleteSemanticSchedule rho hpositive hthreshold rounds)) =
      diagonalAResource
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold rounds) := by sorry
