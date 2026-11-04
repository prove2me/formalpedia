-- Prove2me | Theorems.Thm_ThreeSum_RawAKeyLists_records_length
-- name    : ThreeSum.RawAKeyLists.records_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:52:33.425069+00:00
-- url     : https://prove2.me/theorems/2c8e0402-6e18-4ade-b95f-44a1d07214f6
-- title:
--   Raw AKey Lists: records length
-- statement:
--   The Raw AKey Lists construction uses the records length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L29-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawAKeyLists.lean#L29-L32

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000

theorem ThreeSum.RawAKeyLists.records_length (xs : List ℤ) : (records xs).length=3*xs.length := by sorry
