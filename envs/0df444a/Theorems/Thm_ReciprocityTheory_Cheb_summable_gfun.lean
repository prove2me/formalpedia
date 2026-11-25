-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_summable_gfun
-- name    : ReciprocityTheory.Cheb.summable_gfun
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:49:28.966052+00:00
-- url     : https://prove2.me/theorems/9b2fd7ef-fb09-5b3a-9955-9202d05248d4
-- title:
--   Cheb: summable gfun
-- statement:
--   The Cheb construction uses the summable gfun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SummableGfun.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SummableGfun.lean#L11-L19

import Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA
import Definitions.Def_ReciprocityTheory_Chebotarev_CTrick
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Definitions.Def_ReciprocityTheory_Chebotarev_SummableGfun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.Units Filter Topology Set
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.summable_gfun {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l)
    (c : NZIdeal E) {s : ℝ} (hs : 1 < s) : Summable (gfun χ c s) := by sorry
