-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_hh18GammaInf_eq_sInf
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.hh18GammaInf_eq_sInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:39:02.717384+00:00
-- url     : https://prove2.me/theorems/2d853f62-cb61-48a8-815f-e448cec4931e
-- title:
--   HH18 Sublogarithmic Entropy: hh18 Gamma Inf eq s Inf
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the hh18 Gamma Inf eq s Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L37-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L37-L37

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.hh18GammaInf_eq_sInf : hh18GammaInf = sInf hh18GammaSet := by sorry
