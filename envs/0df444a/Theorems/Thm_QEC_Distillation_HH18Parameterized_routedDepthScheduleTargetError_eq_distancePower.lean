-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleTargetError_eq_distancePower
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleTargetError_eq_distancePower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:52:18.421074+00:00
-- url     : https://prove2.me/theorems/c3038af0-c2dd-4f23-bc3d-490f77bc68ea
-- title:
--   HH18 Parameterized: routed Depth Schedule Target Error eq distance Power
-- statement:
--   The schedule target is the source-relevant distance power written using
--   the exact punctured Reed--Muller distance formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L134-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L134-L140

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleTargetError_eq_distancePower (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) :
    routedDepthScheduleTargetError w r m epsilon depth =
      (routedDepthIterationScale w r m * epsilon.1) ^
        (binomialTail (r + 1) w ^ depth) := by sorry
