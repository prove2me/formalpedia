-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_parameter_length_pos
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_parameter_length_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:04:46.437342+00:00
-- url     : https://prove2.me/theorems/2ccdcab3-77d4-45bc-a530-04d147eacd7a
-- title:
--   HH18 Sublogarithmic Entropy: selected parameter length pos
-- statement:
--   The selected finite length is positive, derived from its binomial tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L225-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L225-L244

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_parameter_length_pos (A D j : Nat)
    (_hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    0 < parameterLength A D j := by sorry
