-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthYieldFactor_eq_actualStageSuccessProduct
-- name    : QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_eq_actualStageSuccessProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:28:59.039989+00:00
-- url     : https://prove2.me/theorems/5523b6b4-babd-476f-9a72-c7dff6e46804
-- title:
--   HH18 Protocol: hh18 Depth Yield Factor eq actual Stage Success Product
-- statement:
--   The finite yield product is the product of the success probabilities of
--   the actual independently indexed stage runs.  This is accounting for fresh
--   resources, not an assertion of a joint all-stage event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L633-L644
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L633-L644

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

theorem QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_eq_actualStageSuccessProduct
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18DepthYieldFactor epsilon hsmall depth : ℝ) =
      ∏ stage : Fin depth,
        (hh18ActualStageRun epsilon hsmall stage.1).successProbability := by sorry
