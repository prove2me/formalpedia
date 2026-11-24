-- Prove2me | Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_preimage_tailSum_logCone
-- name    : ReciprocityTheory.ThetaSummability.Est.preimage_tailSum_logCone
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:23.866467+00:00
-- url     : https://prove2.me/theorems/2fa35bfe-3fa9-4a3b-9787-268be46a6177
-- title:
--   Est: preimage tail Sum log Cone
-- statement:
--   The Est construction uses the preimage tail Sum log Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeChange.lean#L87-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeChange.lean#L87-L88

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

theorem ReciprocityTheory.ThetaSummability.Est.preimage_tailSum_logCone (c : ℝ) : tailSum ⁻¹' logCone r c = lowerBox r c := by sorry
