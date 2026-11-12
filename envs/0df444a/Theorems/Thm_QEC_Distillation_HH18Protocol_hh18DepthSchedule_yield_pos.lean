-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_yield_pos
-- name    : QEC.Distillation.HH18Protocol.hh18DepthSchedule_yield_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:47:44.422581+00:00
-- url     : https://prove2.me/theorems/433d56d3-481f-4e71-8205-71c1c881480f
-- title:
--   HH18 Protocol: hh18 Depth Schedule yield pos
-- statement:
--   Every finite actual schedule yield is strictly positive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1304-L1308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1304-L1308

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

theorem QEC.Distillation.HH18Protocol.hh18DepthSchedule_yield_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    0 < (hh18DepthScheduleYieldFactor epsilon hsmall depth : ℝ) := by sorry
