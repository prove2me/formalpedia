-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_re_psum_one_le
-- name    : ReciprocityTheory.Cheb.re_psum_one_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:35.076108+00:00
-- url     : https://prove2.me/theorems/9458e34b-f2e5-4ea2-bb97-adcb343ee1b6
-- title:
--   Cheb: re psum one le
-- statement:
--   The Cheb construction uses the re psum one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycOrth.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycOrth.lean#L87-L90

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.re_psum_one_le (l : ℕ) [NeZero l] (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    (Psum E (1 : DirichletCharacter ℂ l) s).re ≤ PE E s := by sorry
