-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_oneLevelPooledExpectedYield
-- name    : QEC.Distillation.HH18Protocol.oneLevelPooledExpectedYield
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:31:22.992571+00:00
-- url     : https://prove2.me/theorems/0788265c-02b0-4c60-83ea-a8c1afba12f0
-- title:
--   HH18 Protocol: one Level Pooled Expected Yield
-- statement:
--   Pooled expected yield is the sum of actual block yields, with no
--   all-blocks-success event introduced.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1055-L1063
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1055-L1063

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

theorem QEC.Distillation.HH18Protocol.oneLevelPooledExpectedYield
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (count : Nat) :
    DependentBatch.pooledExpectedAcceptedPorts count
      (oneLevelFlaggedPool epsilon count) =
        (count : ℝ) * endpointWeight (noisyResources epsilon) .accepted := by sorry
