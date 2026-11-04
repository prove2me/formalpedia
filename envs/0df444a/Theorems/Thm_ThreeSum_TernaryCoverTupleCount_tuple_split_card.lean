-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverTupleCount_tuple_split_card
-- name    : ThreeSum.TernaryCoverTupleCount.tuple_split_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:23.229204+00:00
-- url     : https://prove2.me/theorems/f520192c-97df-4930-9164-dd0821c0b197
-- title:
--   Ternary Cover Tuple Count: tuple split card
-- statement:
--   The Ternary Cover Tuple Count construction uses the tuple split card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTupleCount.lean#L34-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTupleCount.lean#L34-L64

import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
import Mathlib.Data.Fin.Tuple.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverTupleCount
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverTupleCount
open Finset TernaryCoverRankFibers TernaryCoverPairStep
variable {K E ι : Type*} [Field K] [Fintype E] [Fintype ι] [DecidableEq K]

theorem ThreeSum.TernaryCoverTupleCount.tuple_split_card (left right : E → ι → K) (n : ℕ)
    (S : Submodule K (Fin (n+1) → K × K)) :
    (tupleSet left right (n+1) S).card =
      (pairedSet left right (tupleColumn left right)
        (S.map (splitRows (K := K) n).toLinearMap)).card := by sorry
