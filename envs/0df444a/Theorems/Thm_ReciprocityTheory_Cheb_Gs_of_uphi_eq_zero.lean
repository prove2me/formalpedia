-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_Gs_of_uphi_eq_zero
-- name    : ReciprocityTheory.Cheb.Gs_of_uphi_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:05.336649+00:00
-- url     : https://prove2.me/theorems/38800905-312b-5f75-b133-62a53bacc9a5
-- title:
--   Cheb: Gs of uphi eq zero
-- statement:
--   The Cheb construction uses the Gs of uphi eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/RpowNegFinrankSubOne.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/RpowNegFinrankSubOne.lean#L22-L24

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

theorem ReciprocityTheory.Cheb.Gs_of_uphi_eq_zero {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) {x : mixedSpace E}
    (hx : uphi x = 0) : Gs χ s x = 0 := by sorry
