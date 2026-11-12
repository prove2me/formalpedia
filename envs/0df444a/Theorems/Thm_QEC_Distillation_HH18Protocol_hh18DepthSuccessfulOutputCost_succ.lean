-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSuccessfulOutputCost_succ
-- name    : QEC.Distillation.HH18Protocol.hh18DepthSuccessfulOutputCost_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:32:25.207027+00:00
-- url     : https://prove2.me/theorems/011860fb-cf3a-4f61-9d64-41b5a99874eb
-- title:
--   HH18 Protocol: hh18 Depth Successful Output Cost succ
-- statement:
--   Restarting one fresh HH18 layer multiplies the actual successful-output
--   cost by fifteen and divides by that layer's measured accepted mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1174-L1191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1174-L1191

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

theorem QEC.Distillation.HH18Protocol.hh18DepthSuccessfulOutputCost_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthSuccessfulOutputCost epsilon hsmall (depth + 1) =
      15 * hh18DepthSuccessfulOutputCost epsilon hsmall depth /
        rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) := by sorry
