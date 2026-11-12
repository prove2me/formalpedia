-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18OneLevelProtocolFamily_run
-- name    : QEC.Distillation.HH18Protocol.hh18OneLevelProtocolFamily_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:30:58.899532+00:00
-- url     : https://prove2.me/theorems/4ece132a-2b34-4411-8b0f-c75cc88ea5a0
-- title:
--   HH18 Protocol: hh18 One Level Protocol Family run
-- statement:
--   The family protocol's run is the literal resource-decoded physical run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1011-L1015
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1011-L1015

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

theorem QEC.Distillation.HH18Protocol.hh18OneLevelProtocolFamily_run
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    ((hh18OneLevelProtocolFamily epsilon).protocol PUnit.unit).run =
      resourceDecodedRun (noisyResources epsilon) := by sorry
