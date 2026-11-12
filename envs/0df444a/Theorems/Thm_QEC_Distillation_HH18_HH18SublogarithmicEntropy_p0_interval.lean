-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_interval
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:42:45.257195+00:00
-- url     : https://prove2.me/theorems/390a4961-477d-417f-83a1-4e257b809109
-- title:
--   HH18 Sublogarithmic Entropy: p0 interval
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the p0 interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L151-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L151-L152

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_interval : (1 / 6 : ℝ) < p0R ∧ p0R < 1 / 3 := by sorry
