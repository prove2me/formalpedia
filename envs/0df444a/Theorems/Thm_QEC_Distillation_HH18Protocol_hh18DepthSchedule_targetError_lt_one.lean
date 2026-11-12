-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_targetError_lt_one
-- name    : QEC.Distillation.HH18Protocol.hh18DepthSchedule_targetError_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:33:20.231467+00:00
-- url     : https://prove2.me/theorems/3019cf1b-157c-4611-a3d9-b662622a2075
-- title:
--   HH18 Protocol: hh18 Depth Schedule target Error lt one
-- statement:
--   Initial scaled smallness makes every compiled target strictly below one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1269-L1293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1269-L1293

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

theorem QEC.Distillation.HH18Protocol.hh18DepthSchedule_targetError_lt_one
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthScheduleTargetError epsilon depth < 1 := by sorry
