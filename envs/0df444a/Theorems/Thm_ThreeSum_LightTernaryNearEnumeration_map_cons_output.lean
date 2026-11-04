-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_map_cons_output
-- name    : ThreeSum.LightTernaryNearEnumeration.map_cons_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:46.48818+00:00
-- url     : https://prove2.me/theorems/0a9e1a03-52da-40fe-8abf-951f315ac4ef
-- title:
--   Light Ternary Near Enumeration: map cons output
-- statement:
--   The Light Ternary Near Enumeration construction uses the map cons output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumeration.lean#L37-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumeration.lean#L37-L44

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryNearEnumeration.map_cons_output (qs : List ℕ) (D pref r : ℕ) :
    (words qs D).map (fun rs => ((pref+code (r::rs) : ℕ) : ℤ)) =
      output qs D (pref+digitCode r*4^qs.length) := by sorry
