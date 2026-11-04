-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_mem_setLayer
-- name    : ThreeSum.QueryCoordinates.mem_setLayer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:15.25877+00:00
-- url     : https://prove2.me/theorems/cfb2835b-8c89-46c2-b1f4-0e0b9af345c1
-- title:
--   Query Coordinates: mem set Layer
-- statement:
--   The Query Coordinates construction uses the mem set Layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L102-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L102-L120

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

theorem ThreeSum.QueryCoordinates.mem_setLayer (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) (s : Finset ℕ) :
    s ∈ setLayer xs k ↔ s ⊆ xs.toFinset ∧ s.card = k := by sorry
