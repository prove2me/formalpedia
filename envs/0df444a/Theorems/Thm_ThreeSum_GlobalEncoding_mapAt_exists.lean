-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_mapAt_exists
-- name    : ThreeSum.GlobalEncoding.mapAt_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:26.961908+00:00
-- url     : https://prove2.me/theorems/ba2ced97-b010-49e2-8b66-ed663456a364
-- title:
--   Global Encoding: map At exists
-- statement:
--   The Global Encoding construction uses the map At exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L40-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L40-L42

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments

theorem ThreeSum.GlobalEncoding.mapAt_exists {h : ℕ} {w : Weight (512 * h) (LocalField h)}
    (hw : w ∈ localSchedule h) : ∃ i : Occurrence h, mapAt h i = w := by sorry
