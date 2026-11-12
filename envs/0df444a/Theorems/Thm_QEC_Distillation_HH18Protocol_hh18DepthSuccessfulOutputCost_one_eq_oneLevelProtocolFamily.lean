-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSuccessfulOutputCost_one_eq_oneLevelProtocolFamily
-- name    : QEC.Distillation.HH18Protocol.hh18DepthSuccessfulOutputCost_one_eq_oneLevelProtocolFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:32:26.10811+00:00
-- url     : https://prove2.me/theorems/9fb0a076-4e04-4e41-b964-f9c1f7c378f4
-- title:
--   HH18 Protocol: hh18 Depth Successful Output Cost one eq one Level Protocol Family
-- statement:
--   Source-neutral depth-one handoff for downstream accounting: the derived
--   finite depth cost is the actual #458 one-level family cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1160-L1170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1160-L1170

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

theorem QEC.Distillation.HH18Protocol.hh18DepthSuccessfulOutputCost_one_eq_oneLevelProtocolFamily
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) :
    hh18DepthSuccessfulOutputCost epsilon hsmall 1 =
      (hh18OneLevelProtocolFamily epsilon).successfulOutputCost PUnit.unit := by sorry
