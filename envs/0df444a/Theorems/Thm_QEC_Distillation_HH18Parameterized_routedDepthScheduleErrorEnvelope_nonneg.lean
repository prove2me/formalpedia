-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleErrorEnvelope_nonneg
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleErrorEnvelope_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:51:04.711561+00:00
-- url     : https://prove2.me/theorems/b377f4a8-4dbe-40aa-9918-923f336becd9
-- title:
--   HH18 Parameterized: routed Depth Schedule Error Envelope nonneg
-- statement:
--   The uniform envelope is nonnegative at every finite depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L165-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L165-L173

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleErrorEnvelope_nonneg (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) :
    0 ≤ routedDepthErrorEnvelope w r m epsilon depth := by sorry
