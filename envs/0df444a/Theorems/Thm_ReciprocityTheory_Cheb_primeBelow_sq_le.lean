-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_primeBelow_sq_le
-- name    : ReciprocityTheory.Cheb.primeBelow_sq_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:49:12.100174+00:00
-- url     : https://prove2.me/theorems/e6ec7066-4fbc-543a-bb56-bea7b020e4b8
-- title:
--   Cheb: prime Below sq le
-- statement:
--   The Cheb construction uses the prime Below sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L26-L33

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

theorem ReciprocityTheory.Cheb.primeBelow_sq_le (q : Prm E) (h : ¬ (Nrm q).Prime) : primeBelow q ^ 2 ≤ Nrm q := by sorry
