-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_tendsto_log_parameterDistance_div
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.tendsto_log_parameterDistance_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:04:11.834071+00:00
-- url     : https://prove2.me/theorems/dc95a942-5d6d-4844-a8f0-e991404da150
-- title:
--   HH18 Sublogarithmic Entropy: tendsto log parameter Distance div
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the tendsto log parameter Distance div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L678-L722
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L678-L722

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.tendsto_log_parameterDistance_div (A D : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindowL : D < 6 * A)
    (hwindowU : 3 * A < D) :
    Tendsto
      (fun j : Nat => Real.log (parameterDistance A D j : ℝ) / j)
      atTop (𝓝 (parameterDistanceLimit A D)) := by sorry
