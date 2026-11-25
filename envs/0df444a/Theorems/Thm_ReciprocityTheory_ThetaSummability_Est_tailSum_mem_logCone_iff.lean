-- Prove2me | Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_tailSum_mem_logCone_iff
-- name    : ReciprocityTheory.ThetaSummability.Est.tailSum_mem_logCone_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:16.578412+00:00
-- url     : https://prove2.me/theorems/98f61651-046a-4e40-9c34-0b3b9f4a3201
-- title:
--   Est: tail Sum mem log Cone iff
-- statement:
--   The Est construction uses the tail Sum mem log Cone iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeChange.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeChange.lean#L83-L85

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

theorem ReciprocityTheory.ThetaSummability.Est.tailSum_mem_logCone_iff (c : ℝ) (y : Fin r → ℝ) :
    tailSum y ∈ logCone r c ↔ y ∈ lowerBox r c := by sorry
