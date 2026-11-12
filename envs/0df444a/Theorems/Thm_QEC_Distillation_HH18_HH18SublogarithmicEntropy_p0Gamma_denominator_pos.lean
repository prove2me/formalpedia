-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0Gamma_denominator_pos
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0Gamma_denominator_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:30:49.239633+00:00
-- url     : https://prove2.me/theorems/cdbc2db5-e295-4e89-9843-d5bf7cfd5ed5
-- title:
--   HH18 Sublogarithmic Entropy: p0 Gamma denominator pos
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the p0 Gamma denominator pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L543-L546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L543-L546

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0Gamma_denominator_pos :
    0 < hh18BinaryEntropy (3 * p0R) := by sorry
