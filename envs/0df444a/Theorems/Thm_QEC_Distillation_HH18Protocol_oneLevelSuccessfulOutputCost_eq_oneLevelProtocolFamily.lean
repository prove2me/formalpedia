-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_oneLevelSuccessfulOutputCost_eq_oneLevelProtocolFamily
-- name    : QEC.Distillation.HH18Protocol.oneLevelSuccessfulOutputCost_eq_oneLevelProtocolFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:45:52.886283+00:00
-- url     : https://prove2.me/theorems/3644af03-9f91-4b92-bec3-449616ac7a8e
-- title:
--   HH18 Protocol: one Level Successful Output Cost eq one Level Protocol Family
-- statement:
--   The finite one-level slot cost is exactly the corresponding #458 family
--   successful-output cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1027-L1043
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1027-L1043

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

theorem QEC.Distillation.HH18Protocol.oneLevelSuccessfulOutputCost_eq_oneLevelProtocolFamily
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    oneLevelSuccessfulOutputCost epsilon =
      (hh18OneLevelProtocolFamily epsilon).successfulOutputCost PUnit.unit := by sorry
