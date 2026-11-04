-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyEnumeration_globalKeys_length
-- name    : ThreeSum.GlobalKeyEnumeration.globalKeys_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:00.41201+00:00
-- url     : https://prove2.me/theorems/aeca230a-3fc7-4582-8b46-dac4fc798c8b
-- title:
--   Global Key Enumeration: global Keys length
-- statement:
--   The Global Key Enumeration construction uses the global Keys length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L120-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L120-L122

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem ThreeSum.GlobalKeyEnumeration.globalKeys_length (h J : ℕ) :
    (globalKeys h J).length=scheduleSize h^J*outputCount (512*h) h^J := by sorry
