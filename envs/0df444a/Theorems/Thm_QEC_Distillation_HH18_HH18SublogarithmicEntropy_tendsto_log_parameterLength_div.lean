-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_tendsto_log_parameterLength_div
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.tendsto_log_parameterLength_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:03:51.288207+00:00
-- url     : https://prove2.me/theorems/7e043c1d-21e4-4700-9ebd-cfc1f773b253
-- title:
--   HH18 Sublogarithmic Entropy: tendsto log parameter Length div
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the tendsto log parameter Length div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L547-L637
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L547-L637

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.tendsto_log_parameterLength_div (A D : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) :
    Tendsto
      (fun j : Nat => Real.log (parameterLength A D j : ℝ) / j)
      atTop (𝓝 (parameterLengthLimit D)) := by sorry
