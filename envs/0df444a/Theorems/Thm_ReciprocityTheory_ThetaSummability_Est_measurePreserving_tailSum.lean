-- Prove2me | Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_measurePreserving_tailSum
-- name    : ReciprocityTheory.ThetaSummability.Est.measurePreserving_tailSum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:28.660805+00:00
-- url     : https://prove2.me/theorems/b843a0f2-fc48-4156-bb45-f7fee43699b5
-- title:
--   Est: measure Preserving tail Sum
-- statement:
--   The Est construction uses the measure Preserving tail Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeChange.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeChange.lean#L65-L70

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

theorem ReciprocityTheory.ThetaSummability.Est.measurePreserving_tailSum :
    MeasurePreserving (tailSum (r := r)) volume volume := by sorry
