-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_stageResource_succ
-- name    : QEC.Distillation.HH18Protocol.hh18DepthSchedule_stageResource_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:34:52.985119+00:00
-- url     : https://prove2.me/theorems/1c5f818e-5ba5-415c-9f32-0745172c4e5d
-- title:
--   HH18 Protocol: hh18 Depth Schedule stage Resource succ
-- statement:
--   The physical next stage is exactly the accepted output transported into
--   the next input family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1600-L1606
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1600-L1606

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

theorem QEC.Distillation.HH18Protocol.hh18DepthSchedule_stageResource_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthStageResource epsilon hsmall (depth + 1) =
      fun _ => hh18AcceptedOutputAsNextInput
        (hh18ErrorIteration epsilon hsmall depth) := by sorry
