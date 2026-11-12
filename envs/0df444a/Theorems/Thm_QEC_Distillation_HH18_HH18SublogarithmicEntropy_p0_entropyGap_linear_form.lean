-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_entropyGap_linear_form
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_entropyGap_linear_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:03:22.479788+00:00
-- url     : https://prove2.me/theorems/515c8099-ea88-46f0-9f3d-28b8493fa0a7
-- title:
--   HH18 Sublogarithmic Entropy: p0 entropy Gap linear form
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the p0 entropy Gap linear form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L504-L515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L504-L515

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_entropyGap_linear_form :
    p0EntropyGap =
      - (280286193 / 500000 : ℝ) * Real.log 2
      - (811887 / 2000 : ℝ) * p0A
      + (2188113 / 2000 : ℝ) * p0B
      + (275229693 / 1000000 : ℝ) * p0C
      + (63770307 / 1000000 : ℝ) * p0D := by sorry
