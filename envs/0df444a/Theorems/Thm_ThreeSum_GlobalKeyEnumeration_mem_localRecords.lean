-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyEnumeration_mem_localRecords
-- name    : ThreeSum.GlobalKeyEnumeration.mem_localRecords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:51.973757+00:00
-- url     : https://prove2.me/theorems/740b5bd6-47c9-4cb5-83df-b08912b20a3b
-- title:
--   Global Key Enumeration: mem local Records
-- statement:
--   The Global Key Enumeration construction uses the mem local Records property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L62-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L62-L63

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

theorem ThreeSum.GlobalKeyEnumeration.mem_localRecords (h : ℕ) (b : OutputBlock h) : b ∈ localRecords h := by sorry
