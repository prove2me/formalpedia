-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_log_norm_eq_sum
-- name    : ReciprocityTheory.Cheb.log_norm_eq_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:52.656829+00:00
-- url     : https://prove2.me/theorems/4cdf630d-e510-58c5-b3dd-5de1b359f97d
-- title:
--   Cheb: log norm eq sum
-- statement:
--   The Cheb construction uses the log norm eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L85-L88

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.log_norm_eq_sum {z : mixedSpace E} (hz : ∀ w, normAtPlace w z ≠ 0) :
    Real.log (mixedEmbedding.norm z) = ∑ w, (mult w : ℝ) * Real.log (normAtPlace w z) := by sorry
