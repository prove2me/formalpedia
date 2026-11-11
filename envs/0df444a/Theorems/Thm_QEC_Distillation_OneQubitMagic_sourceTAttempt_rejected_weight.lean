-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTAttempt_rejected_weight
-- name    : QEC.Distillation.OneQubitMagic.sourceTAttempt_rejected_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:01:36.079209+00:00
-- url     : https://prove2.me/theorems/8ba2aba6-c2ac-4c41-bfd5-9f79a73d3e15
-- title:
--   One Qubit Magic: source TAttempt rejected weight
-- statement:
--   The One Qubit Magic construction uses the source TAttempt rejected weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L670-L671
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L670-L671

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

theorem QEC.Distillation.OneQubitMagic.sourceTAttempt_rejected_weight : sourceTAttempt.rejectedWeight = 1 / 3 := by sorry
