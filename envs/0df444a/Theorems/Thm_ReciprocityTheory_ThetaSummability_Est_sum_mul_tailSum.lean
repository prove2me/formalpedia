-- Prove2me | Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_sum_mul_tailSum
-- name    : ReciprocityTheory.ThetaSummability.Est.sum_mul_tailSum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:01.561618+00:00
-- url     : https://prove2.me/theorems/9cddb51d-3a98-529b-9ea9-a17b3cd61144
-- title:
--   Est: sum mul tail Sum
-- statement:
--   The Est construction uses the sum mul tail Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeExp.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeExp.lean#L9-L14

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

theorem ReciprocityTheory.ThetaSummability.Est.sum_mul_tailSum (s y : Fin r → ℝ) :
    ∑ i, s i * tailSum y i = ∑ k, partialSum s k * y k := by sorry
