-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_mem_parameterInterval
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_mem_parameterInterval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:43:04.526187+00:00
-- url     : https://prove2.me/theorems/3944d387-1d7d-4a70-a7b4-55ae418dd843
-- title:
--   HH18 Sublogarithmic Entropy: p0 mem parameter Interval
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the p0 mem parameter Interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L154-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L154-L155

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_mem_parameterInterval : p0R ∈ hh18ParameterInterval := by sorry
