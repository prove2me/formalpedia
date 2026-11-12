-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleSuccessfulOutputCost_eq
-- name    : QEC.Distillation.HH18Protocol.hh18DepthScheduleSuccessfulOutputCost_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:33:30.03172+00:00
-- url     : https://prove2.me/theorems/b47203ac-afa6-411d-baba-0e9a1f6c5bfe
-- title:
--   HH18 Protocol: hh18 Depth Schedule Successful Output Cost eq
-- statement:
--   The typed finite-slot cost has its exact actual fifteen-to-one form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1311-L1320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1311-L1320

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

theorem QEC.Distillation.HH18Protocol.hh18DepthScheduleSuccessfulOutputCost_eq
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    DependentBatch.typedSuccessfulOutputCost
      (hh18DepthScheduleInputSlots depth)
      (hh18DepthScheduleOutputSlots depth)
      (hh18DepthScheduleYieldFactor epsilon hsmall depth) =
        (15 : ℝ) ^ depth /
          (hh18DepthScheduleYieldFactor epsilon hsmall depth : ℝ) := by sorry
