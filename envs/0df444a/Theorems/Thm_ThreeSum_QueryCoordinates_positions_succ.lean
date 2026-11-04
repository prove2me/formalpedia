-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_positions_succ
-- name    : ThreeSum.QueryCoordinates.positions_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:28.213534+00:00
-- url     : https://prove2.me/theorems/7274ca8e-e010-48a4-a476-9f9ed80e8ff6
-- title:
--   Query Coordinates: positions succ
-- statement:
--   The Query Coordinates construction uses the positions succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L26-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L26-L28

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

theorem ThreeSum.QueryCoordinates.positions_succ {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    positions Q (j+1) = positions Q j ++ if j ∈ natPositions Q then [j] else [] := by sorry
