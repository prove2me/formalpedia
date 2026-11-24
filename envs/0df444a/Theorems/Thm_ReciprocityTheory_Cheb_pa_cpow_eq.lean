-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_pa_cpow_eq
-- name    : ReciprocityTheory.Cheb.pa_cpow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:50.734452+00:00
-- url     : https://prove2.me/theorems/da165d9f-061f-4296-820e-c3e317fed3c6
-- title:
--   Cheb: pa cpow eq
-- statement:
--   The Cheb construction uses the pa cpow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L9-L13

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

theorem ReciprocityTheory.Cheb.pa_cpow_eq (n : ℕ) (s : ℝ) :
    ((n : ℂ) ^ (-(s : ℂ))) = (((n : ℝ) ^ (-s) : ℝ) : ℂ) := by sorry
