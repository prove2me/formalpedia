-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18ParameterSequence_p0_parameters_admissible
-- name    : QEC.Distillation.HH18.HH18ParameterSequence.p0_parameters_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:38:18.580664+00:00
-- url     : https://prove2.me/theorems/478f17c5-440c-4d2f-a79b-ea2d7066a2df
-- title:
--   HH18 Parameter Sequence: p0 parameters admissible
-- statement:
--   At each positive index, the strict-bound sequence has exactly the approved
--   rational slope and satisfies all natural-number hypotheses of HH18 Theorem 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSequence.lean#L28-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSequence.lean#L28-L40

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18ParameterSequence
open Coding.PuncturedReedMuller

theorem QEC.Distillation.HH18.HH18ParameterSequence.p0_parameters_admissible (j : Nat) (hj : 0 < j) :
    p0M j = 3 * p0R j + 1 ∧
      (p0W j : ℚ) = 3 * (p0R j : ℚ) * p0 ∧
      Admissible (p0W j) (p0R j) (p0M j) := by sorry
