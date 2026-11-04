-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverHighMoment_jointEvent_rows
-- name    : ThreeSum.TernaryCoverHighMoment.jointEvent_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:25.441234+00:00
-- url     : https://prove2.me/theorems/217dc827-275f-42f8-855a-09e62dbcf8eb
-- title:
--   Ternary Cover High Moment: joint Event rows
-- statement:
--   The Ternary Cover High Moment construction uses the joint Event rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHighMoment.lean#L85-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHighMoment.lean#L85-L104

import Definitions.Def_Submission_ThreeSum_TernaryCoverTupleCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Definitions.Def_Submission_ThreeSum_TernaryCoverMoments
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverHighMoment
open Finset TernaryCoverRankFibers TernaryCoverTupleCount
open TernaryCoverRelations TernaryCoverUniformRank TernaryCoverMoments
open scoped BigOperators
variable {K E σ : Type*} [Field K] [Fintype E] [Fintype σ] [DecidableEq σ]
variable [Fintype K] [DecidableEq K]

theorem ThreeSum.TernaryCoverHighMoment.jointEvent_rows (left right : E → σ → Fin 3) (a b : K) {k : ℕ} (es : Fin k → E) :
    jointEvent (rawEvents (K := K) left right a b) es =
      prescribedEvent (rows left right es) (flattenPairs k (fun _ => (a,b))) := by sorry
