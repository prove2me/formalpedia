-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_rat_num_den_in_window
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.rat_num_den_in_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:04:10.673188+00:00
-- url     : https://prove2.me/theorems/4e869bdf-e87d-45b5-abc7-0d492a78b623
-- title:
--   HH18 Sublogarithmic Entropy: rat num den in window
-- statement:
--   A rational strictly inside the source window has a positive natural
--   numerator and denominator, the cleared upper bound, and its exact quotient
--   representation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L50-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L50-L76

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.rat_num_den_in_window {q : ℚ}
    (hqL : (1 / 6 : ℚ) < q) (hqU : q < (1 / 3 : ℚ)) :
    let A : Nat := q.num.natAbs
    let D : Nat := q.den
    0 < A ∧ 0 < D ∧ 3 * A < D ∧ q = (A : ℚ) / D := by sorry
