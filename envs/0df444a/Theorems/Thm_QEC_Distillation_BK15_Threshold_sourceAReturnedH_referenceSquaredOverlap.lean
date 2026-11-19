-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_sourceAReturnedH_referenceSquaredOverlap
-- name    : QEC.Distillation.BK15.Threshold.sourceAReturnedH_referenceSquaredOverlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:28:26.160903+00:00
-- url     : https://prove2.me/theorems/44c80faf-10a4-4835-9f22-362039189995
-- title:
--   Threshold: source AReturned H reference Squared Overlap
-- statement:
--   The inverse transport makes the reference-H squared overlap of the
--   returned density exactly the positive-A overlap of the actual accepted output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1121-L1136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1121-L1136

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic

theorem QEC.Distillation.BK15.Threshold.sourceAReturnedH_referenceSquaredOverlap
    (sigma : DensityOperator QubitSpace) :
    projectionSquaredOverlap (hProjector hReference)
        (sourceA0Transport.symm.conjDensity sigma) =
      aInputSquaredOverlap sigma := by sorry
