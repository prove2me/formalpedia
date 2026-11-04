-- Prove2me | Theorems.Thm_ThreeSum_QueryCoordinates_output_eq_sublists
-- name    : ThreeSum.QueryCoordinates.output_eq_sublists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:13:39.662391+00:00
-- url     : https://prove2.me/theorems/73ef3a34-6a8f-415e-bd93-e004d7f5e284
-- title:
--   Query Coordinates: output eq sublists
-- statement:
--   The Query Coordinates construction uses the output eq sublists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L122-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/QueryCoordinates.lean#L122-L138

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

theorem ThreeSum.QueryCoordinates.output_eq_sublists (weight : ℕ → ℕ) (L k pref : ℕ) :
    LightWeightedEnumeration.output weight L k pref =
      (((List.range L).reverse).sublistsLen k).map
        (fun xs => ((pref+(xs.map weight).sum : ℕ) : ℤ)) := by sorry
