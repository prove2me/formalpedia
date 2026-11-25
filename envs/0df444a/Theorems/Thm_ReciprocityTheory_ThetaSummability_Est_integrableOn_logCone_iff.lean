-- Prove2me | Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_integrableOn_logCone_iff
-- name    : ReciprocityTheory.ThetaSummability.Est.integrableOn_logCone_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:45.955697+00:00
-- url     : https://prove2.me/theorems/02bc041b-5f6c-532f-8862-27226b64c1f6
-- title:
--   Est: integrable On log Cone iff
-- statement:
--   The Est construction uses the integrable On log Cone iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeChange.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeChange.lean#L95-L98

import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeDefs
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ThetaSummability ReciprocityTheory.ThetaSummability.Est
open MeasureTheory Finset
variable {r : ℕ}

theorem ReciprocityTheory.ThetaSummability.Est.integrableOn_logCone_iff (c : ℝ) (f : (Fin r → ℝ) → ℝ) :
    IntegrableOn f (logCone r c) ↔ IntegrableOn (fun y => f (tailSum y)) (lowerBox r c) := by sorry
