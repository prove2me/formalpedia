-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_depthTwoChildInputSlot_injective
-- name    : QEC.Distillation.HH18Protocol.depthTwoChildInputSlot_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:31:46.154862+00:00
-- url     : https://prove2.me/theorems/bbdd5ed0-3ea3-4777-ba01-1f7ec1a704d6
-- title:
--   HH18 Protocol: depth Two Child Input Slot injective
-- statement:
--   Each routed child input has a distinct parent source; this is the concrete
--   no-duplicate resource routing fact needed before a subsequent physical layer
--   can consume these outputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1085-L1091
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1085-L1091

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic

theorem QEC.Distillation.HH18Protocol.depthTwoChildInputSlot_injective (port : BatchOutputPort) :
    Function.Injective (fun parent : Fin resourceCount =>
      depthTwoRouting (DependentBatch.childInputSlot port parent)) := by sorry
