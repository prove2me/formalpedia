-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTEvenBranch_xor_discard
-- name    : QEC.Distillation.OneQubitMagic.sourceTEvenBranch_xor_discard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:14:36.724739+00:00
-- url     : https://prove2.me/theorems/b1fca9f9-b87a-44b3-919c-f658ce6e8d94
-- title:
--   One Qubit Magic: source TEven Branch xor discard
-- statement:
--   The accepted branch passed through the existing XOR/discard channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L623-L628
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L623-L628

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

theorem QEC.Distillation.OneQubitMagic.sourceTEvenBranch_xor_discard :
    (QuantumChannel.comp secondQubitDiscard
      (QuantumChannel.unitaryConj xorTransport)).mapDensity sourceTEvenBranch =
      zzEvenBranchFirstDensity sourceTTwoQubitState sourceTEvenWeight_pos := by sorry
