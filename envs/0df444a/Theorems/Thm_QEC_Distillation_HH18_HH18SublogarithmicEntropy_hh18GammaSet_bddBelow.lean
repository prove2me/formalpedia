-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_hh18GammaSet_bddBelow
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.hh18GammaSet_bddBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:35:01.310948+00:00
-- url     : https://prove2.me/theorems/4aa8805b-66c1-4b67-9418-96f1f09190da
-- title:
--   HH18 Sublogarithmic Entropy: hh18 Gamma Set bdd Below
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the hh18 Gamma Set bdd Below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L101-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L101-L106

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.hh18GammaSet_bddBelow : BddBelow hh18GammaSet := by sorry
