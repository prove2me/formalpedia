-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0LinearLower_eq_gap
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0LinearLower_eq_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:02:38.762256+00:00
-- url     : https://prove2.me/theorems/db2e18a9-f880-4a5c-adf8-300d1217da81
-- title:
--   HH18 Sublogarithmic Entropy: p0 Linear Lower eq gap
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the p0 Linear Lower eq gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L436-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L436-L439

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0LinearLower_eq_gap : p0LinearLower = (p0CertifiedGapQ : ℝ) := by sorry
