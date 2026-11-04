-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_positions_nodup
-- name    : ThreeSum.QueryCoordinates.positions_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:48:09.563095+00:00
-- url     : https://prove2.me/theorems/0e388c06-eb68-4690-8eae-5ad7e676dc4e
-- title:
--   Query Coordinates: positions nodup
-- statement:
--   The Query Coordinates construction uses the positions nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L34-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L34-L35

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

theorem ThreeSum.QueryCoordinates.positions_nodup {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    (positions Q j).Nodup := by sorry
