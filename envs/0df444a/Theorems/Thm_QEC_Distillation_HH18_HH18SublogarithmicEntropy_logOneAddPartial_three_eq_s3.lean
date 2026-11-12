-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_logOneAddPartial_three_eq_s3
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAddPartial_three_eq_s3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:36:26.212204+00:00
-- url     : https://prove2.me/theorems/e5fe80a9-8dd1-4e8a-a2c5-61753fbf3632
-- title:
--   HH18 Sublogarithmic Entropy: log One Add Partial three eq s3
-- statement:
--   The three-term truncation uses exactly the odd indices `0, 1, 2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L254-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L254-L257

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAddPartial_three_eq_s3 (a : ℝ) :
    logOneAddPartial a 3 = s3 (a / (a + 2)) := by sorry
