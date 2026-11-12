-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthYieldFactor_succ_actualStageRun
-- name    : QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_succ_actualStageRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:46:37.004123+00:00
-- url     : https://prove2.me/theorems/3031f70b-3bb7-4948-b44b-052f07a13a6c
-- title:
--   HH18 Protocol: hh18 Depth Yield Factor succ actual Stage Run
-- statement:
--   The restart factor is the success probability of the actual final stage
--   run, as identified by the physical stage-run invariant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1113-L1120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1113-L1120

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

theorem QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_succ_actualStageRun
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18DepthYieldFactor epsilon hsmall (depth + 1) : ℝ) =
      (hh18DepthYieldFactor epsilon hsmall depth : ℝ) *
        (hh18ActualStageRun epsilon hsmall depth).successProbability := by sorry
