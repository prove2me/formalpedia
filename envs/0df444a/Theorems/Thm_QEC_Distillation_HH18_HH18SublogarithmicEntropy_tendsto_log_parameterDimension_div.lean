-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_tendsto_log_parameterDimension_div
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.tendsto_log_parameterDimension_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:04:23.395006+00:00
-- url     : https://prove2.me/theorems/a022e65a-c78e-4fa8-beee-1831df60b0c5
-- title:
--   HH18 Sublogarithmic Entropy: tendsto log parameter Dimension div
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the tendsto log parameter Dimension div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L639-L676
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L639-L676

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.tendsto_log_parameterDimension_div (A D : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) :
    Tendsto
      (fun j : Nat => Real.log (parameterDimension A D j : ℝ) / j)
      atTop (𝓝 (parameterDimensionLimit A D)) := by sorry
