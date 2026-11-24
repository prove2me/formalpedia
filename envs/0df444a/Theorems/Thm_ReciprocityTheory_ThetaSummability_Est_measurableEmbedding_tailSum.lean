-- Prove2me | Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_measurableEmbedding_tailSum
-- name    : ReciprocityTheory.ThetaSummability.Est.measurableEmbedding_tailSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:31.847487+00:00
-- url     : https://prove2.me/theorems/cea4d130-0cc3-4f22-b015-47c2796de695
-- title:
--   Est: measurable Embedding tail Sum
-- statement:
--   The Est construction uses the measurable Embedding tail Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeChange.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeChange.lean#L80-L81

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

theorem ReciprocityTheory.ThetaSummability.Est.measurableEmbedding_tailSum : MeasurableEmbedding (tailSum (r := r)) := by sorry
