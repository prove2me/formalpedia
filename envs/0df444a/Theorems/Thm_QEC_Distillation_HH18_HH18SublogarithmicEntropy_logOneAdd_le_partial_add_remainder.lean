-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_logOneAdd_le_partial_add_remainder
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAdd_le_partial_add_remainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:43:24.558412+00:00
-- url     : https://prove2.me/theorems/1653630d-8ead-42cd-8dfd-448fddca9082
-- title:
--   HH18 Sublogarithmic Entropy: log One Add le partial add remainder
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the log One Add le partial add remainder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L180-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L180-L240

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAdd_le_partial_add_remainder {a : ℝ} (ha : 0 ≤ a) (N : Nat) :
    Real.log (1 + a) ≤ logOneAddPartial a N +
      logOneAddRemainder (a / (a + 2)) N := by sorry
