-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_depth_from_selectedDoublePowerTarget
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.depth_from_selectedDoublePowerTarget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:34:26.809847+00:00
-- url     : https://prove2.me/theorems/2750a028-16d6-4ac3-8b1b-d5c4fec61989
-- title:
--   HH18 Sublogarithmic Entropy: depth from selected Double Power Target
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the depth from selected Double Power Target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L330-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L330-L340

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.depth_from_selectedDoublePowerTarget {q : ℝ} {A D j z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hD : 0 < D)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    (z : ℝ) =
      Real.log
        (Real.log (1 / selectedDoublePowerTarget q A D j z) /
          Real.log (1 / q)) / Real.log (parameterDistance A D j) := by sorry
