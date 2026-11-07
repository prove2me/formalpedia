-- Prove2me | Theorems.Thm_QEC_Distillation_MagicStateDistillationProtocol_inputModel_permits
-- name    : QEC.Distillation.MagicStateDistillationProtocol.inputModel_permits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:58:35.662193+00:00
-- url     : https://prove2.me/theorems/9adf5e86-e421-4db3-bc71-356b9fc698fd
-- title:
--   Magic State Distillation Protocol: input Model permits
-- statement:
--   The protocol's noisy resource family is permitted by its selected model.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L386-L389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L386-L389

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
set_option autoImplicit false
universe u
open QEC
open QEC.Distillation
open Semantics
open scoped BigOperators
open QEC.Distillation.MagicStateDistillationProtocol
variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]

theorem QEC.Distillation.MagicStateDistillationProtocol.inputModel_permits
    (protocol : MagicStateDistillationProtocol Resource Input Output) :
    protocol.inputErrorModel.Permits protocol.run.noisyInput := by sorry
