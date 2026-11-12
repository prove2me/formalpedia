-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_logOneAdd_partial_le
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAdd_partial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:36:35.379366+00:00
-- url     : https://prove2.me/theorems/b983089a-988a-4aa5-b1a9-7bdf9bb9975b
-- title:
--   HH18 Sublogarithmic Entropy: log One Add partial le
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the log One Add partial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L171-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L171-L178

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAdd_partial_le {a : ℝ} (ha : 0 ≤ a) (N : Nat) :
    logOneAddPartial a N ≤ Real.log (1 + a) := by sorry
