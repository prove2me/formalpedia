-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_total_weights
-- name    : ThreeSum.QueryCoordinates.total_weights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:47:18.153047+00:00
-- url     : https://prove2.me/theorems/a964944b-7186-45fd-a25b-d4a72fad556f
-- title:
--   Query Coordinates: total weights
-- statement:
--   The Query Coordinates construction uses the total weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L80-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L80-L83

import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
set_option autoImplicit false
open ThreeSum ThreeSum.QueryCoordinates
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.QueryCoordinates.total_weights {W : ℕ} (Q : Finset (Fin W)) :
    LightWeightedEnumeration.total (weights Q) Q.card = subsetMask Q := by sorry
