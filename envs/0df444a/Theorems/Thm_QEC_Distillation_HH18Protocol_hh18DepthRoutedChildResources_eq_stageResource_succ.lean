-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthRoutedChildResources_eq_stageResource_succ
-- name    : QEC.Distillation.HH18Protocol.hh18DepthRoutedChildResources_eq_stageResource_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:34:04.403255+00:00
-- url     : https://prove2.me/theorems/b4cc4427-32d9-45ca-bbc5-24197d6c44e0
-- title:
--   HH18 Protocol: hh18 Depth Routed Child Resources eq stage Resource succ
-- statement:
--   The routed actual child resources are exactly the compiled next-stage
--   resource family, by the existing physical accepted-output handoff.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L851-L859
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L851-L859

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

theorem QEC.Distillation.HH18Protocol.hh18DepthRoutedChildResources_eq_stageResource_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthRoutedChildResources epsilon hsmall depth =
      hh18DepthStageResource epsilon hsmall (depth + 1) := by sorry
