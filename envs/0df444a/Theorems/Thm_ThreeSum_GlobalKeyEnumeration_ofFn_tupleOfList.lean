-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyEnumeration_ofFn_tupleOfList
-- name    : ThreeSum.GlobalKeyEnumeration.ofFn_tupleOfList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:50.906275+00:00
-- url     : https://prove2.me/theorems/e1145e02-b797-419f-8ae7-898bc05d3e90
-- title:
--   Global Key Enumeration: of Fn tuple Of List
-- statement:
--   The Global Key Enumeration construction uses the of Fn tuple Of List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L73-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L73-L76

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

theorem ThreeSum.GlobalKeyEnumeration.ofFn_tupleOfList {α : Type*} {J : ℕ} (xs : List α) (hlen : xs.length=J) :
    List.ofFn (tupleOfList xs hlen)=xs := by sorry
