-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selectedCSSCode_parameters
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.selectedCSSCode_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:33:05.723656+00:00
-- url     : https://prove2.me/theorems/5d51b6d8-78ab-4be3-88dd-27b5012f8a85
-- title:
--   HH18 Sublogarithmic Entropy: selected CSSCode parameters
-- statement:
--   The exact #759 physical, logical, carrier, and semantic-distance counts
--   are respectively the selector's n, k, 2^k, and d.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/SelectedCode.lean#L40-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/SelectedCode.lean#L40-L55

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_SelectedCode
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding
open Coding.PuncturedReedMuller
open QEC.Distillation.HH18PuncturedReedMuller

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.selectedCSSCode_parameters (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    Length (ZMod 2) (PhysicalSite (parameterM D j) (parameterW A j)) =
        parameterLength A D j ∧
      Length (ZMod 2) (PhysicalSite (parameterM D j) (parameterW A j)) -
          Dimension (xCode (parameterW A j) (parameterR D j) (parameterM D j)) -
          Dimension (zCode (parameterW A j) (parameterR D j) (parameterM D j)) =
        parameterDimension A D j ∧
      Module.finrank Complex
          (selectedCSSCode A D j hA hD hwindow hj).stabilizer.code.carrier =
        2 ^ parameterDimension A D j ∧
      StabilizerCode.SemanticStabilizerDistance
          (sourceValidStabilizer
            (selected_parameter_admissible A D j hA hD hwindow hj))
          (parameterDistance A D j) := by sorry
