-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_natCast_mem_of_not_coprime
-- name    : ReciprocityTheory.Cheb.natCast_mem_of_not_coprime
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:26.403838+00:00
-- url     : https://prove2.me/theorems/5843a12c-c080-4e6d-bb92-902732280d99
-- title:
--   Cheb: nat Cast mem of not coprime
-- statement:
--   The Cheb construction uses the nat Cast mem of not coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L36-L47

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
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

theorem ReciprocityTheory.Cheb.natCast_mem_of_not_coprime (E : Type) [Field E] [NumberField E] (n : ℕ) (q : Prm E)
    (h : ¬ Nat.Coprime (Nrm q) n) : ((n : ℕ) : 𝓞 E) ∈ q.asIdeal := by sorry
