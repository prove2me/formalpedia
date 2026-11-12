-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_threePow_mul_logGrowthBase_le_log
-- name    : QEC.Distillation.HH18Protocol.hh18DepthSchedule_threePow_mul_logGrowthBase_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:48:56.236058+00:00
-- url     : https://prove2.me/theorems/175b39b9-e3ce-486d-909d-45e6a2c5cc01
-- title:
--   HH18 Protocol: hh18 Depth Schedule three Pow mul log Growth Base le log
-- statement:
--   The initial log base multiplied by the literal cubic depth is no larger
--   than the logarithm of the reciprocal compiled target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1376-L1407
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1376-L1407

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

theorem QEC.Distillation.HH18Protocol.hh18DepthSchedule_threePow_mul_logGrowthBase_le_log
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (depth : Nat) :
    (3 : ℝ) ^ depth * hh18DepthScheduleLogGrowthBase epsilon ≤
      Real.log (1 / hh18DepthScheduleTargetError epsilon depth) := by sorry
