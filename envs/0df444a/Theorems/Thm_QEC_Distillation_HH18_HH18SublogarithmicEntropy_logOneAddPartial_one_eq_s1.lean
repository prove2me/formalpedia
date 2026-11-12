-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_logOneAddPartial_one_eq_s1
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAddPartial_one_eq_s1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:01:31.549296+00:00
-- url     : https://prove2.me/theorems/9f462a58-3005-4661-983b-963cb08cdf69
-- title:
--   HH18 Sublogarithmic Entropy: log One Add Partial one eq s1
-- statement:
--   The one-term truncation, with the `Finset.range 1` index made explicit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L249-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L249-L251

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAddPartial_one_eq_s1 (a : ℝ) :
    logOneAddPartial a 1 = s1 (a / (a + 2)) := by sorry
