-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_logC_lower
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_logC_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:02:37.054024+00:00
-- url     : https://prove2.me/theorems/c2c022f0-fa23-4bfd-b765-060bfa4295a2
-- title:
--   HH18 Sublogarithmic Entropy: p0 log C lower
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the p0 log C lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L377-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L377-L387

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_logC_lower : logCLower ≤ p0C := by sorry
