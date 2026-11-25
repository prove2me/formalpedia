-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_mem_primesOverFinset_primeBelow
-- name    : ReciprocityTheory.Cheb.mem_primesOverFinset_primeBelow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:50.134129+00:00
-- url     : https://prove2.me/theorems/b0d5045a-6c1d-4cc8-97a4-2235c0ede569
-- title:
--   Cheb: mem primes Over Finset prime Below
-- statement:
--   The Cheb construction uses the mem primes Over Finset prime Below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L35-L42

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.mem_primesOverFinset_primeBelow (q : Prm E) :
    q.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((primeBelow q : ℕ) : ℤ)}) (𝓞 E) := by sorry
