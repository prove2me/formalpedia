-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyEnumeration_globalKeys_eq_map
-- name    : ThreeSum.GlobalKeyEnumeration.globalKeys_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:56.577199+00:00
-- url     : https://prove2.me/theorems/9e47099a-0135-498e-bae1-ed75a13ad38e
-- title:
--   Global Key Enumeration: global Keys eq map
-- statement:
--   Exact array identity, not merely equality of the set of key values.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L106-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L106-L118

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

theorem ThreeSum.GlobalKeyEnumeration.globalKeys_eq_map (h J : ℕ) :
    globalKeys h J=(globalRecords h J).map globalKey := by sorry
