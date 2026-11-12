-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTAttempt_rejected_branch_normalized
-- name    : QEC.Distillation.OneQubitMagic.sourceTAttempt_rejected_branch_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:00:55.138196+00:00
-- url     : https://prove2.me/theorems/74c5bfc4-e3bb-463d-a1c4-070b6a92b025
-- title:
--   One Qubit Magic: source TAttempt rejected branch normalized
-- statement:
--   The One Qubit Magic construction uses the source TAttempt rejected branch normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L677-L679
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L677-L679

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

theorem QEC.Distillation.OneQubitMagic.sourceTAttempt_rejected_branch_normalized :
    LinearMap.trace Complex TwoQubitSpace sourceTAttempt.rejectedBranch.toOperator = 1 := by sorry
