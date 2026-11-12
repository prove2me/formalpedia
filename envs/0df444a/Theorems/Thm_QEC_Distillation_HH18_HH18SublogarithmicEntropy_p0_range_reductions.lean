-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_range_reductions
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_range_reductions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:35:46.226079+00:00
-- url     : https://prove2.me/theorems/5853d20b-2c1d-4a1a-b784-acf05f59213d
-- title:
--   HH18 Sublogarithmic Entropy: p0 range reductions
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the p0 range reductions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L321-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L321-L332

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_range_reductions :
    p0A = Real.log (1 + aA) ∧
      p0B = Real.log (1 + aB) ∧
      p0C = Real.log (1 + aC) ∧
      p0D = Real.log (1 + aD) := by sorry
