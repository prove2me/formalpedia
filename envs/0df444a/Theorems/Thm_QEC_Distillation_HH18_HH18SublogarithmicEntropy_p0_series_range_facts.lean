-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_series_range_facts
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_series_range_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:26:41.970439+00:00
-- url     : https://prove2.me/theorems/8eb81a3e-fe20-443b-aebf-ca019b9a5f35
-- title:
--   HH18 Sublogarithmic Entropy: p0 series range facts
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the p0 series range facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L291-L296
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L291-L296

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_series_range_facts :
    0 ≤ yA ∧ yA ≤ 1 / 25 ∧
      0 ≤ yB ∧ yB < 1 ∧
      0 ≤ yC ∧ yC < 1 ∧
      0 ≤ yD ∧ yD < 1 := by sorry
