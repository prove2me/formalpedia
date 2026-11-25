-- Prove2me | Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_integral_exp_logCone
-- name    : ReciprocityTheory.ThetaSummability.Est.integral_exp_logCone
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:38:23.109368+00:00
-- url     : https://prove2.me/theorems/24c2b81b-1777-41d0-b2e8-40eaecc6bfc7
-- title:
--   Est: integral exp log Cone
-- statement:
--   The Est construction uses the integral exp log Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeExp.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeExp.lean#L33-L42

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

theorem ReciprocityTheory.ThetaSummability.Est.integral_exp_logCone (c : ℝ) {s : Fin r → ℝ} (hs : ∀ k, partialSum s k < 0) :
    ∫ x in logCone r c, exp (∑ i, s i * x i) =
      ∏ k, exp (partialSum s k * c) / (-partialSum s k) := by sorry
