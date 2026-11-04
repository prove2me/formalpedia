-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_output_coordinates
-- name    : ThreeSum.QueryCoordinates.output_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:13:43.353417+00:00
-- url     : https://prove2.me/theorems/37073e05-9470-4812-852b-20ed6d92170a
-- title:
--   Query Coordinates: output coordinates
-- statement:
--   The Query Coordinates construction uses the output coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L170-L183
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L170-L183

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

theorem ThreeSum.QueryCoordinates.output_coordinates (xs : List ℕ) (k pref : ℕ) :
    LightWeightedEnumeration.output (fun i => (xs.map fun a => 2^a)[i]?.getD 0)
        xs.length k pref =
      ((xs.reverse).sublistsLen k).map
        (fun ys => ((pref+(ys.map fun a => 2^a).sum : ℕ) : ℤ)) := by sorry
