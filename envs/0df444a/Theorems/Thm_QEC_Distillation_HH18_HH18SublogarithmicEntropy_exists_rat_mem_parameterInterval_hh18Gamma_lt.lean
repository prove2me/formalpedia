-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_exists_rat_mem_parameterInterval_hh18Gamma_lt
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.exists_rat_mem_parameterInterval_hh18Gamma_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:01:00.034598+00:00
-- url     : https://prove2.me/theorems/6cf1abd6-ed07-44d7-955a-e3383cd18333
-- title:
--   HH18 Sublogarithmic Entropy: exists rat mem parameter Interval hh18 Gamma lt
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the exists rat mem parameter Interval hh18 Gamma lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L108-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L108-L135

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.exists_rat_mem_parameterInterval_hh18Gamma_lt (delta : ℝ)
    (hdelta : 0 < delta) :
    ∃ q : ℚ, ((q : ℝ) ∈ hh18ParameterInterval) ∧
      hh18Gamma (q : ℝ) < hh18GammaInf + delta := by sorry
