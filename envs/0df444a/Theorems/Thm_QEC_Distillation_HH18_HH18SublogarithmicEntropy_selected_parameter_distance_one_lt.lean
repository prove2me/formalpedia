-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_parameter_distance_one_lt
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_parameter_distance_one_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:37:40.394202+00:00
-- url     : https://prove2.me/theorems/bf890a11-adcb-4d14-a9af-3a7f3c1073cc
-- title:
--   HH18 Sublogarithmic Entropy: selected parameter distance one lt
-- statement:
--   The selected binomial-tail distance is genuinely larger than one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L257-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L257-L285

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_parameter_distance_one_lt (A D j : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    1 < parameterDistance A D j := by sorry
