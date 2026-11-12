-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_entropy_expansions
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_entropy_expansions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:03:23.136209+00:00
-- url     : https://prove2.me/theorems/8c61aeb2-ac52-4d98-9b6b-acb67889419a
-- title:
--   HH18 Sublogarithmic Entropy: p0 entropy expansions
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the p0 entropy expansions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L490-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L490-L502

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_entropy_expansions :
    Real.binEntropy p0R = p0R * (2 * Real.log 2 - p0A) + p0q * p0B ∧
      Real.binEntropy p0u = p0u * p0C + p0v * (2 * Real.log 2 + p0D) := by sorry
