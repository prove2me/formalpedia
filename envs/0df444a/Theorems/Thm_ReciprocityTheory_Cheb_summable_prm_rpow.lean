-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_summable_prm_rpow
-- name    : ReciprocityTheory.Cheb.summable_prm_rpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:15.022617+00:00
-- url     : https://prove2.me/theorems/1d1e587c-7a0b-45f6-8192-30b79fd0d6b3
-- title:
--   Cheb: summable prm rpow
-- statement:
--   The Cheb construction uses the summable prm rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L135-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L135-L143

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
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

theorem ReciprocityTheory.Cheb.summable_prm_rpow (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) := by sorry
