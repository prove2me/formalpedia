-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_visits_le
-- name    : ThreeSum.TernaryNearEnumeration.visits_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:23.068766+00:00
-- url     : https://prove2.me/theorems/0d75cf64-1abf-4890-ae4e-80c32bb65e83
-- title:
--   Ternary Near Enumeration: visits le
-- statement:
--   The Ternary Near Enumeration construction uses the visits le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L197-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L197-L213

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryEnumeration_visits_le

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.visits_le (qs : List ℕ) (D : ℕ) :
    visits qs D ≤ (qs.length+1)*(words qs D).length := by sorry
