-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTGlobalPhase_norm
-- name    : QEC.Distillation.OneQubitMagic.sourceTGlobalPhase_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T15:02:58.919578+00:00
-- url     : https://prove2.me/theorems/a9e1a48c-a744-4b26-be4e-4021174a554e
-- title:
--   One Qubit Magic: source TGlobal Phase norm
-- statement:
--   The displayed global phase has unit norm, so it is physically inessential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L617-L620
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L617-L620

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

theorem QEC.Distillation.OneQubitMagic.sourceTGlobalPhase_norm : ‖sourceTGlobalPhase‖ = 1 := by sorry
