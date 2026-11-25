-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_pa_log_bdd
-- name    : ReciprocityTheory.Cheb.pa_log_bdd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:20.501477+00:00
-- url     : https://prove2.me/theorems/97995581-92a7-4eed-bfe2-890d9370aa3b
-- title:
--   Cheb: pa log bdd
-- statement:
--   The Cheb construction uses the pa log bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L65-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L65-L77

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

theorem ReciprocityTheory.Cheb.pa_log_bdd {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |-Real.log (1 - x) - x| ≤ 2 * x ^ 2 := by sorry
