-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_cyor_norm_cpow
-- name    : ReciprocityTheory.Cheb.cyor_norm_cpow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:55.408431+00:00
-- url     : https://prove2.me/theorems/4774a1ae-2cf1-45f2-b732-4a7089e779f0
-- title:
--   Cheb: cyor norm cpow
-- statement:
--   The Cheb construction uses the cyor norm cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycOrth.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycOrth.lean#L14-L17

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

theorem ReciprocityTheory.Cheb.cyor_norm_cpow (q : Prm E) (s : ℝ) :
    ‖((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ = ((Nrm q : ℕ) : ℝ) ^ (-s) := by sorry
