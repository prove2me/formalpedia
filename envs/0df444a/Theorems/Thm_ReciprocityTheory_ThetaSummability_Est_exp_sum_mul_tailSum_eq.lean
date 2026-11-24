-- Prove2me | Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_exp_sum_mul_tailSum_eq
-- name    : ReciprocityTheory.ThetaSummability.Est.exp_sum_mul_tailSum_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:30.678797+00:00
-- url     : https://prove2.me/theorems/8dc51dca-a52c-4394-bfab-0c45e3abf914
-- title:
--   Est: exp sum mul tail Sum eq
-- statement:
--   The Est construction uses the exp sum mul tail Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeExp.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeExp.lean#L16-L20

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

theorem ReciprocityTheory.ThetaSummability.Est.exp_sum_mul_tailSum_eq (s : Fin r → ℝ) :
    (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) =
      fun y => ∏ k, (fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t)) k (y k) := by sorry
