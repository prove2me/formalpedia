-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_logA_remainder_bound
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_logA_remainder_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:02:18.767397+00:00
-- url     : https://prove2.me/theorems/cae70db5-386e-444c-bb38-6d34217f25bb
-- title:
--   HH18 Sublogarithmic Entropy: p0 log A remainder bound
-- statement:
--   The exact A-series parameter is below the rational majorant at `N = 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L309-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L309-L311

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_logA_remainder_bound :
    logOneAddRemainder (aA / (aA + 2)) 1 ≤ 1 / 23400 := by sorry
