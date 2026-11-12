-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_continuousAt_hh18Gamma_of_mem_parameterInterval
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.continuousAt_hh18Gamma_of_mem_parameterInterval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:01:08.942306+00:00
-- url     : https://prove2.me/theorems/596ccd15-951b-4504-8eeb-0e8c742df115
-- title:
--   HH18 Sublogarithmic Entropy: continuous At hh18 Gamma of mem parameter Interval
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the continuous At hh18 Gamma of mem parameter Interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L80-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L80-L94

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.continuousAt_hh18Gamma_of_mem_parameterInterval {p : ℝ}
    (hp : p ∈ hh18ParameterInterval) : ContinuousAt hh18Gamma p := by sorry
