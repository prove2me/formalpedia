-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTEvenOutput_norm
-- name    : QEC.Distillation.OneQubitMagic.sourceTEvenOutput_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:25:48.732052+00:00
-- url     : https://prove2.me/theorems/1f08e025-4dd4-4b2e-a29b-316b84970fd1
-- title:
--   One Qubit Magic: source TEven Output norm
-- statement:
--   The One Qubit Magic construction uses the source TEven Output norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L611-L614
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L611-L614

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

theorem QEC.Distillation.OneQubitMagic.sourceTEvenOutput_norm : ‖hadamardOperator sourceTEvenFirstQubit‖ = 1 := by sorry
