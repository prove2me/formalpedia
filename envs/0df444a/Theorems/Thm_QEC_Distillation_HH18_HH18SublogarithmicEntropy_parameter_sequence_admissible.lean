-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_parameter_sequence_admissible
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.parameter_sequence_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:37:19.578525+00:00
-- url     : https://prove2.me/theorems/3dce321e-462d-48de-914b-edf580294fe0
-- title:
--   HH18 Sublogarithmic Entropy: parameter sequence admissible
-- statement:
--   The doubled cleared sequence has `m = 3r+1`, the exact rational slope,
--   and the actual natural-number admissibility condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L80-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L80-L111

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.parameter_sequence_admissible
    (A D j : Nat) (hA : 0 < A) (hD : 0 < D)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    parameterM D j = 3 * parameterR D j + 1 ∧
      (parameterW A j : ℚ) =
        3 * (parameterR D j : ℚ) * ((A : ℚ) / D) ∧
      Admissible (parameterW A j) (parameterR D j) (parameterM D j) := by sorry
