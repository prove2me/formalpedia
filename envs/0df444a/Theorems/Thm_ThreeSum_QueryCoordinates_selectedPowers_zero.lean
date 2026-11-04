-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_zero
-- name    : ThreeSum.QueryCoordinates.selectedPowers_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:47:31.93639+00:00
-- url     : https://prove2.me/theorems/0e42ef5e-4c3c-4547-9cc3-d4140dfed47b
-- title:
--   Query Coordinates: selected Powers zero
-- statement:
--   The Query Coordinates construction uses the selected Powers zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L57-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L57-L58

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

theorem ThreeSum.QueryCoordinates.selectedPowers_zero {W : ℕ} (Q : Finset (Fin W)) :
    selectedPowers Q 0 = [] := by sorry
