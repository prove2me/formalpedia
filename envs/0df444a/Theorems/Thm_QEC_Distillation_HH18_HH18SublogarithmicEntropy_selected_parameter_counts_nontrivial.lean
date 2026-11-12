-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_parameter_counts_nontrivial
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_parameter_counts_nontrivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:37:46.083397+00:00
-- url     : https://prove2.me/theorems/fefc940b-ebe7-4dc6-aae3-3b28e8557a72
-- title:
--   HH18 Sublogarithmic Entropy: selected parameter counts nontrivial
-- statement:
--   Positivity and distance nontriviality are derived from the exact selected
--   counts, not supplied by a schedule conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L289-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L289-L295

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_parameter_counts_nontrivial (A D j : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    0 < parameterLength A D j ∧ 0 < parameterDimension A D j ∧
      1 < parameterDistance A D j := by sorry
