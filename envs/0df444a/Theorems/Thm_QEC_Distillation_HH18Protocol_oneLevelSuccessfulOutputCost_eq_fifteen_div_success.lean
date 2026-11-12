-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_oneLevelSuccessfulOutputCost_eq_fifteen_div_success
-- name    : QEC.Distillation.HH18Protocol.oneLevelSuccessfulOutputCost_eq_fifteen_div_success
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:29:35.363205+00:00
-- url     : https://prove2.me/theorems/0f945ac0-d006-4bd3-9ae1-91d4a3df0d44
-- title:
--   HH18 Protocol: one Level Successful Output Cost eq fifteen div success
-- statement:
--   The actual successful-output cost is finite and is computed from the
--   fifteen physical slots and the measured success probability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L953-L961
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L953-L961

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

theorem QEC.Distillation.HH18Protocol.oneLevelSuccessfulOutputCost_eq_fifteen_div_success
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    oneLevelSuccessfulOutputCost epsilon =
      15 / endpointWeight (noisyResources epsilon) .accepted := by sorry
