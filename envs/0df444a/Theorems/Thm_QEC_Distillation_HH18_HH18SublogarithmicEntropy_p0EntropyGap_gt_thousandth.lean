-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0EntropyGap_gt_thousandth
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0EntropyGap_gt_thousandth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:43:41.823426+00:00
-- url     : https://prove2.me/theorems/04761e82-069a-4b8d-baca-4a55ed021f20
-- title:
--   HH18 Sublogarithmic Entropy: p0 Entropy Gap gt thousandth
-- statement:
--   The analytic part has been reduced to the exact fourteen-term rational
--   certificate, whose gap is strictly larger than `1 / 1000`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L523-L536
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean#L523-L536

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0EntropyGap_gt_thousandth : (1 / 1000 : ℝ) < p0EntropyGap := by sorry
