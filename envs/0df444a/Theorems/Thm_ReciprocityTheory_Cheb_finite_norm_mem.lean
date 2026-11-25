-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_finite_norm_mem
-- name    : ReciprocityTheory.Cheb.finite_norm_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:57.653041+00:00
-- url     : https://prove2.me/theorems/5b0d9a90-0db3-4ab2-af39-e9638dca3585
-- title:
--   Cheb: finite norm mem
-- statement:
--   The Cheb construction uses the finite norm mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L98-L104

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

theorem ReciprocityTheory.Cheb.finite_norm_mem (T : Finset ℕ) : {q : Prm E | Nrm q ∈ T}.Finite := by sorry
