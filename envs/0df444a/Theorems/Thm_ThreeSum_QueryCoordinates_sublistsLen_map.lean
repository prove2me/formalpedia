-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_sublistsLen_map
-- name    : ThreeSum.QueryCoordinates.sublistsLen_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:13:44.633741+00:00
-- url     : https://prove2.me/theorems/1f44d467-b4d1-462e-8132-fd733febaff5
-- title:
--   Query Coordinates: sublists Len map
-- statement:
--   The Query Coordinates construction uses the sublists Len map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L153-L161
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L153-L161

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

theorem ThreeSum.QueryCoordinates.sublistsLen_map (f : ℕ → ℕ) (xs : List ℕ) (k : ℕ) :
    (xs.map f).sublistsLen k = (xs.sublistsLen k).map (List.map f) := by sorry
