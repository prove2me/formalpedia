-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_mem_positions
-- name    : ThreeSum.QueryCoordinates.mem_positions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:47:12.951567+00:00
-- url     : https://prove2.me/theorems/aae43357-013e-49e8-868d-8325a3fb1ce6
-- title:
--   Query Coordinates: mem positions
-- statement:
--   The Query Coordinates construction uses the mem positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L30-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L30-L32

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

theorem ThreeSum.QueryCoordinates.mem_positions {W : ℕ} (Q : Finset (Fin W)) (j i : ℕ) :
    i ∈ positions Q j ↔ i < j ∧ i ∈ natPositions Q := by sorry
