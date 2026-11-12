-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthYieldFactor_succ
-- name    : QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:45:36.754255+00:00
-- url     : https://prove2.me/theorems/8014c120-f798-4f10-9692-69a7153b084d
-- title:
--   HH18 Protocol: hh18 Depth Yield Factor succ
-- statement:
--   The finite actual layer-yield product gains exactly the next stage's
--   measured accepted mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1095-L1109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1095-L1109

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

theorem QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18DepthYieldFactor epsilon hsmall (depth + 1) : ℝ) =
      (hh18DepthYieldFactor epsilon hsmall depth : ℝ) *
        rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) := by sorry
