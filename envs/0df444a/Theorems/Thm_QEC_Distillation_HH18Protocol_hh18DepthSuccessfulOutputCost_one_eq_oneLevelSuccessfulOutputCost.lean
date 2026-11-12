-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSuccessfulOutputCost_one_eq_oneLevelSuccessfulOutputCost
-- name    : QEC.Distillation.HH18Protocol.hh18DepthSuccessfulOutputCost_one_eq_oneLevelSuccessfulOutputCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:47:04.537978+00:00
-- url     : https://prove2.me/theorems/2844da79-4d91-4c9f-85b2-2d798ed88829
-- title:
--   HH18 Protocol: hh18 Depth Successful Output Cost one eq one Level Successful Output Cost
-- statement:
--   At depth one, the literal depth accounting cost is the actual one-level
--   successful-output cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1138-L1156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1138-L1156

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

theorem QEC.Distillation.HH18Protocol.hh18DepthSuccessfulOutputCost_one_eq_oneLevelSuccessfulOutputCost
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) :
    hh18DepthSuccessfulOutputCost epsilon hsmall 1 =
      oneLevelSuccessfulOutputCost epsilon := by sorry
