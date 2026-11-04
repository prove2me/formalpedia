-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_succ
-- name    : ThreeSum.QueryCoordinates.selectedPowers_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:13:37.924398+00:00
-- url     : https://prove2.me/theorems/c8bb6130-48db-42ef-970e-0640a4946b00
-- title:
--   Query Coordinates: selected Powers succ
-- statement:
--   The Query Coordinates construction uses the selected Powers succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L60-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L60-L64

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

theorem ThreeSum.QueryCoordinates.selectedPowers_succ {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    selectedPowers Q (j+1) =
      selectedPowers Q j ++ if j ∈ natPositions Q then [2^j] else [] := by sorry
