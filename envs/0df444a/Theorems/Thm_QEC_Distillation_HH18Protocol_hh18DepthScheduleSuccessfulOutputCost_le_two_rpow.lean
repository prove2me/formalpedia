-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleSuccessfulOutputCost_le_two_rpow
-- name    : QEC.Distillation.HH18Protocol.hh18DepthScheduleSuccessfulOutputCost_le_two_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:51:48.258192+00:00
-- url     : https://prove2.me/theorems/5d29fee0-252b-4799-a590-5b900d49ec07
-- title:
--   HH18 Protocol: hh18 Depth Schedule Successful Output Cost le two rpow
-- statement:
--   The literal successful-output cost is bounded by twice the fixed-block
--   real-power form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1411-L1420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1411-L1420

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

theorem QEC.Distillation.HH18Protocol.hh18DepthScheduleSuccessfulOutputCost_le_two_rpow
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    DependentBatch.typedSuccessfulOutputCost
      (hh18DepthScheduleInputSlots depth)
      (hh18DepthScheduleOutputSlots depth)
      (hh18DepthScheduleYieldFactor epsilon hsmall depth) ≤
        2 * Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma := by sorry
