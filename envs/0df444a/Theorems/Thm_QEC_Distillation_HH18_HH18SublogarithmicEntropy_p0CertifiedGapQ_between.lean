-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0CertifiedGapQ_between
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0CertifiedGapQ_between
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:28:12.69441+00:00
-- url     : https://prove2.me/theorems/c475bc4f-c292-4683-919c-f16eafaaff10
-- title:
--   HH18 Sublogarithmic Entropy: p0 Certified Gap Q between
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the p0 Certified Gap Q between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L421-L424
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L421-L424

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0CertifiedGapQ_between :
    10869 / 10000000 < p0CertifiedGapQ ∧
      p0CertifiedGapQ < 1087 / 1000000 := by sorry
