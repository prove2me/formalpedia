-- Prove2me | Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_summable_and_tsum_pi_prod
-- name    : ReciprocityTheory.ThetaSummability.Est.summable_and_tsum_pi_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:06.975125+00:00
-- url     : https://prove2.me/theorems/80ec94d0-f951-4ed3-a7dd-5e0f7c561d41
-- title:
--   Est: summable and tsum pi prod
-- statement:
--   The Est construction uses the summable and tsum pi prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/LatSumPi.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/LatSumPi.lean#L7-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_LatSumPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ThetaSummability ReciprocityTheory.ThetaSummability.Est
open Module

theorem ReciprocityTheory.ThetaSummability.Est.summable_and_tsum_pi_prod {α : Type*} {q : ℕ} (f : Fin q → α → ℝ)
    (hf0 : ∀ i a, 0 ≤ f i a) (hf : ∀ i, Summable (f i)) :
    Summable (fun x : Fin q → α => ∏ i, f i (x i)) ∧
      ∑' x : Fin q → α, ∏ i, f i (x i) = ∏ i, ∑' a, f i a := by sorry
