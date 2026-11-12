-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_tendsto_selectedDoublePowerTarget_zero
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.tendsto_selectedDoublePowerTarget_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:33:39.350507+00:00
-- url     : https://prove2.me/theorems/263e8eb4-0b9e-45a7-8753-bd5cd28c2488
-- title:
--   HH18 Sublogarithmic Entropy: tendsto selected Double Power Target zero
-- statement:
--   The genuine double-power target tends to zero for the selected distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L313-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L313-L320

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.tendsto_selectedDoublePowerTarget_zero {q : ℝ} {A D j : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hD : 0 < D)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    Tendsto (fun z : Nat => selectedDoublePowerTarget q A D j z)
      atTop (𝓝 0) := by sorry
