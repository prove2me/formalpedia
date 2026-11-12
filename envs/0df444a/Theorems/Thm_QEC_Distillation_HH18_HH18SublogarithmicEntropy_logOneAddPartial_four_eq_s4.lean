-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_logOneAddPartial_four_eq_s4
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAddPartial_four_eq_s4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:02:29.622994+00:00
-- url     : https://prove2.me/theorems/ce8cc252-669e-4c79-8437-867ec1d64359
-- title:
--   HH18 Sublogarithmic Entropy: log One Add Partial four eq s4
-- statement:
--   The four-term truncation uses exactly the odd indices `0, 1, 2, 3`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L260-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L260-L263

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAddPartial_four_eq_s4 (a : ℝ) :
    logOneAddPartial a 4 = s4 (a / (a + 2)) := by sorry
