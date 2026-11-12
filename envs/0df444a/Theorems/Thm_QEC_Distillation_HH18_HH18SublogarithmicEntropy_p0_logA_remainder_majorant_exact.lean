-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_logA_remainder_majorant_exact
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_logA_remainder_majorant_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:26:22.677889+00:00
-- url     : https://prove2.me/theorems/7836c5c8-9886-4595-806d-791344e73930
-- title:
--   HH18 Sublogarithmic Entropy: p0 log A remainder majorant exact
-- statement:
--   Rational majorant used for the one A-term remainder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L304-L306
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L304-L306

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_logA_remainder_majorant_exact :
    logOneAddRemainder (1 / 25 : ℝ) 1 = 1 / 23400 := by sorry
