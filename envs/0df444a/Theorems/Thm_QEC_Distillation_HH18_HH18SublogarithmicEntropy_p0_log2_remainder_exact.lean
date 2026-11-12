-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_log2_remainder_exact
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_log2_remainder_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:01:45.021787+00:00
-- url     : https://prove2.me/theorems/8f52f7ab-1df9-4baf-8de1-33cd5c31a968
-- title:
--   HH18 Sublogarithmic Entropy: p0 log2 remainder exact
-- statement:
--   Exact geometric remainder for the four log-two terms (`N = 4`).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L299-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L299-L301

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_log2_remainder_exact :
    logOneAddRemainder (1 / 3 : ℝ) 4 = 1 / 78732 := by sorry
