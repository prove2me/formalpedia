-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_complements
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_complements
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:43:16.076571+00:00
-- url     : https://prove2.me/theorems/c6b020c8-afb5-4748-b251-60524f08529a
-- title:
--   HH18 Sublogarithmic Entropy: p0 complements
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the p0 complements property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L157-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L157-L162

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_complements :
    p0q = 729371 / 1000000 ∧
      p0u = 811887 / 1000000 ∧
      p0v = 188113 / 1000000 ∧
      0 < p0u ∧ p0u < 1 ∧ 0 < p0v ∧ p0v < 1 := by sorry
