-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_gs_diff_bound
-- name    : ReciprocityTheory.Cheb.gs_diff_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:53.728259+00:00
-- url     : https://prove2.me/theorems/9f24319d-e2a0-44d9-b53b-df81371a1c52
-- title:
--   Cheb: gs diff bound
-- statement:
--   The Cheb construction uses the gs diff bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/RpowNegFinrankSubOne.lean#L26-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/RpowNegFinrankSubOne.lean#L26-L79

import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.gs_diff_bound {l : ℕ} (χ : DirichletCharacter ℂ l) (B : ℝ) :
    ∃ R₀ C : ℝ, ∀ s ∈ Set.Icc (1 : ℝ) 2, ∀ x h : mixedSpace E, ‖h‖ ≤ B → R₀ ≤ ‖x‖ →
      ‖Gs χ s (x + h) - Gs χ s x‖ ≤ C * ‖x‖ ^ (-(Module.finrank ℚ E : ℝ) - 1) := by sorry
