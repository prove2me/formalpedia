-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTEvenOutput_global_phase
-- name    : QEC.Distillation.OneQubitMagic.sourceTEvenOutput_global_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:25:48.54343+00:00
-- url     : https://prove2.me/theorems/15cdbd70-26b1-4d32-87e4-4cc57fd9ebcb
-- title:
--   One Qubit Magic: source TEven Output global phase
-- statement:
--   After XOR, discard, and Hadamard, the accepted source state is exactly
--   `A_{-pi/6}` up to the displayed global phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L592-L609
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L592-L609

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open TwoQubit
open scoped InnerProductSpace TensorProduct

theorem QEC.Distillation.OneQubitMagic.sourceTEvenOutput_global_phase :
    hadamardOperator sourceTEvenFirstQubit =
      sourceTGlobalPhase • phaseState (-Real.pi / 6) := by sorry
