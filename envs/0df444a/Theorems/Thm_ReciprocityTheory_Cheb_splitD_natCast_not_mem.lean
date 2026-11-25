-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitD_natCast_not_mem
-- name    : ReciprocityTheory.Cheb.splitD_natCast_not_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:49:26.713976+00:00
-- url     : https://prove2.me/theorems/eaccf07c-6804-52c5-919a-68a028646f2d
-- title:
--   Cheb: split D nat Cast not mem
-- statement:
--   The Cheb construction uses the split D nat Cast not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitD.lean#L7-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitD.lean#L7-L28

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.splitD_natCast_not_mem (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (hl : ¬ l ∣ Nrm q) : (l : 𝓞 E) ∉ q.asIdeal := by sorry
