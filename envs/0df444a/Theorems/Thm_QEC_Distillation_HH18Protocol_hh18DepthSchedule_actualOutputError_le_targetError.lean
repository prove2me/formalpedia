-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_actualOutputError_le_targetError
-- name    : QEC.Distillation.HH18Protocol.hh18DepthSchedule_actualOutputError_le_targetError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:30:18.370751+00:00
-- url     : https://prove2.me/theorems/6b37715b-67e5-498e-816c-709bffc87eb6
-- title:
--   HH18 Protocol: hh18 Depth Schedule actual Output Error le target Error
-- statement:
--   The recursively reached actual error is bounded by the schedule target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1296-L1301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1296-L1301

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

theorem QEC.Distillation.HH18Protocol.hh18DepthSchedule_actualOutputError_le_targetError
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthScheduleActualOutputError epsilon hsmall depth ≤
      hh18DepthScheduleTargetError epsilon depth := by sorry
