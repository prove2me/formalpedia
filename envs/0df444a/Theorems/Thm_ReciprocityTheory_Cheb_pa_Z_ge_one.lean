-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_pa_Z_ge_one
-- name    : ReciprocityTheory.Cheb.pa_Z_ge_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:49.564821+00:00
-- url     : https://prove2.me/theorems/8969f0cc-7133-4ad2-b4e0-d40314b18c6c
-- title:
--   Cheb: pa Z ge one
-- statement:
--   The Cheb construction uses the pa Z ge one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L110-L114

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

theorem ReciprocityTheory.Cheb.pa_Z_ge_one (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    1 ≤ ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by sorry
