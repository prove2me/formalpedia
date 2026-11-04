-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_positions_toFinset
-- name    : ThreeSum.QueryCoordinates.positions_toFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:47:08.112501+00:00
-- url     : https://prove2.me/theorems/0c1a434d-e33e-4a9d-ae2a-149ccf88fa1d
-- title:
--   Query Coordinates: positions to Finset
-- statement:
--   The Query Coordinates construction uses the positions to Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L41-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L41-L45

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

theorem ThreeSum.QueryCoordinates.positions_toFinset {W : ℕ} (Q : Finset (Fin W)) :
    (positions Q W).toFinset = natPositions Q := by sorry
