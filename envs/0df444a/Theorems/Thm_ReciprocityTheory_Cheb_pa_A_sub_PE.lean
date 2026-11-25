-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_pa_A_sub_PE
-- name    : ReciprocityTheory.Cheb.pa_A_sub_PE
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:47.617483+00:00
-- url     : https://prove2.me/theorems/74239531-e670-43ee-9149-d942102586e7
-- title:
--   Cheb: pa A sub PE
-- statement:
--   The Cheb construction uses the pa A sub PE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L79-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L79-L108

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
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

theorem ReciprocityTheory.Cheb.pa_A_sub_PE (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    |(∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) - PE E s| ≤
      2 * ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by sorry
