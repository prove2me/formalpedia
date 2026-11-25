-- Prove2me | Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_integrableOn_exp_logCone
-- name    : ReciprocityTheory.ThetaSummability.Est.integrableOn_exp_logCone
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:19.008579+00:00
-- url     : https://prove2.me/theorems/93d1a06c-1475-4c65-a32a-772aa7e26abe
-- title:
--   Est: integrable On exp log Cone
-- statement:
--   The Est construction uses the integrable On exp log Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeExp.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeExp.lean#L22-L31

import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ThetaSummability ReciprocityTheory.ThetaSummability.Est
open MeasureTheory Finset Real
variable {r : ℕ}

theorem ReciprocityTheory.ThetaSummability.Est.integrableOn_exp_logCone (c : ℝ) {s : Fin r → ℝ} (hs : ∀ k, partialSum s k < 0) :
    IntegrableOn (fun x => exp (∑ i, s i * x i)) (logCone r c) := by sorry
