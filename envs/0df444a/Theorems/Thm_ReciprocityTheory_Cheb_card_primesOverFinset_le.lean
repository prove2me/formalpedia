-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_card_primesOverFinset_le
-- name    : ReciprocityTheory.Cheb.card_primesOverFinset_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:52.158949+00:00
-- url     : https://prove2.me/theorems/0ace659f-557b-4269-bcbe-d9c029ab20ed
-- title:
--   Cheb: card primes Over Finset le
-- statement:
--   The Cheb construction uses the card primes Over Finset le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L44-L49

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

theorem ReciprocityTheory.Cheb.card_primesOverFinset_le (p : ℕ) (hp : p.Prime) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 E)).card ≤ Module.finrank ℚ E := by sorry
