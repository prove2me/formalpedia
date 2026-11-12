-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleSuccessfulOutputCost_le_cubicEnvelope_polylog
-- name    : QEC.Distillation.HH18Protocol.hh18DepthScheduleSuccessfulOutputCost_le_cubicEnvelope_polylog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:51:48.890341+00:00
-- url     : https://prove2.me/theorems/d1d64b42-385a-4a1b-a98c-37c816878e2f
-- title:
--   HH18 Protocol: hh18 Depth Schedule Successful Output Cost le cubic Envelope polylog
-- statement:
--   The actual finite-depth HH18 cost is bounded by the real-rpow of the
--   compiled cubic-target logarithm with its derived coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1424-L1507
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1424-L1507

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

theorem QEC.Distillation.HH18Protocol.hh18DepthScheduleSuccessfulOutputCost_le_cubicEnvelope_polylog
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    DependentBatch.typedSuccessfulOutputCost
      (hh18DepthScheduleInputSlots depth)
      (hh18DepthScheduleOutputSlots depth)
      (hh18DepthScheduleYieldFactor epsilon hsmall depth) ≤
        hh18DepthScheduleCostCoefficient epsilon *
          Real.rpow
            (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
            hh18DepthScheduleGamma := by sorry
