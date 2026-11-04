-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEnumeration_visits_full_succ
-- name    : ThreeSum.LightTernaryEnumeration.visits_full_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:41.498173+00:00
-- url     : https://prove2.me/theorems/93d1e31f-7692-43e7-aa4a-fce094289ebd
-- title:
--   Light Ternary Enumeration: visits full succ
-- statement:
--   The Light Ternary Enumeration construction uses the visits full succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L47-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L47-L49

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryEnumeration.visits_full_succ {T : ℕ} (hT : 2 ≤ T) (N : ℕ) :
    visits (N+1) T = 1+visits N T+visits N (T-1)+visits N (T-2) := by sorry
