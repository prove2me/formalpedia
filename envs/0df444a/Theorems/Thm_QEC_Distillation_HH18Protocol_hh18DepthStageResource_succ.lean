-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthStageResource_succ
-- name    : QEC.Distillation.HH18Protocol.hh18DepthStageResource_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:28:25.717939+00:00
-- url     : https://prove2.me/theorems/adfbd006-dd65-41a2-bee5-9bde561c6797
-- title:
--   HH18 Protocol: hh18 Depth Stage Resource succ
-- statement:
--   The next physical input family is literally the inverse-phase/dephased
--   accepted output of the preceding actual HH18 stage.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L775-L790
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L775-L790

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

theorem QEC.Distillation.HH18Protocol.hh18DepthStageResource_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthStageResource epsilon hsmall (depth + 1) =
      fun _ => hh18AcceptedOutputAsNextInput (hh18ErrorIteration epsilon hsmall depth) := by sorry
