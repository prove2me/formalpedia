-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_summable_nonprime_norm
-- name    : ReciprocityTheory.Cheb.summable_nonprime_norm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:40.203904+00:00
-- url     : https://prove2.me/theorems/2b83039a-a0a2-5c39-b6bb-976839538f23
-- title:
--   Cheb: summable nonprime norm
-- statement:
--   The Cheb construction uses the summable nonprime norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L75-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L75-L96

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

theorem ReciprocityTheory.Cheb.summable_nonprime_norm :
    Summable (fun q : Prm E => if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) := by sorry
