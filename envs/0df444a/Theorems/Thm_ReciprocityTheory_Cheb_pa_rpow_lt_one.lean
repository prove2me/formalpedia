-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_pa_rpow_lt_one
-- name    : ReciprocityTheory.Cheb.pa_rpow_lt_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:39.41487+00:00
-- url     : https://prove2.me/theorems/c28fe396-1a10-41f4-be64-4cbaec27108b
-- title:
--   Cheb: pa rpow lt one
-- statement:
--   The Cheb construction uses the pa rpow lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L22-L26

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

theorem ReciprocityTheory.Cheb.pa_rpow_lt_one {E : Type} [Field E] [NumberField E] (q : Prm E) {s : ℝ} (hs : 0 < s) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) < 1 := by sorry
