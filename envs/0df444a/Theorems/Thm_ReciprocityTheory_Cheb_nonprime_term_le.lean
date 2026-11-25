-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_nonprime_term_le
-- name    : ReciprocityTheory.Cheb.nonprime_term_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:49:01.160721+00:00
-- url     : https://prove2.me/theorems/fec2c848-39c7-4cf2-989f-c17df99420cd
-- title:
--   Cheb: nonprime term le
-- statement:
--   The Cheb construction uses the nonprime term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L64-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycTail.lean#L64-L73

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

theorem ReciprocityTheory.Cheb.nonprime_term_le (q : Prm E) :
    (if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) ≤ 1 / ((primeBelow q : ℕ) : ℝ) ^ 2 := by sorry
