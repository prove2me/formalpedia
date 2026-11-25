-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_pcl_one_le_re_psum_one
-- name    : ReciprocityTheory.Cheb.pcl_one_le_re_psum_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:08.713146+00:00
-- url     : https://prove2.me/theorems/6bbe0867-5b3a-4423-94f8-e3dd751c131c
-- title:
--   Cheb: pcl one le re psum one
-- statement:
--   The Cheb construction uses the pcl one le re psum one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycOrth.lean#L64-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycOrth.lean#L64-L85

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

theorem ReciprocityTheory.Cheb.pcl_one_le_re_psum_one (l : ℕ) [NeZero l] (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    Pcl E l 1 s ≤ (Psum E (1 : DirichletCharacter ℂ l) s).re := by sorry
