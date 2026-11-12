-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_binEntropy_eq_log_inv_form
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.binEntropy_eq_log_inv_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:02:57.617069+00:00
-- url     : https://prove2.me/theorems/22e3f329-ee34-4d9d-9075-c72e49337ec0
-- title:
--   HH18 Sublogarithmic Entropy: bin Entropy eq log inv form
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the bin Entropy eq log inv form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L446-L450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L446-L450

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.binEntropy_eq_log_inv_form (x : ℝ) :
    Real.binEntropy x =
      x * Real.log (1 / x) + (1 - x) * Real.log (1 / (1 - x)) := by sorry
