-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverHighMoment_raw_high_moment
-- name    : ThreeSum.TernaryCoverHighMoment.raw_high_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:15.107047+00:00
-- url     : https://prove2.me/theorems/e7f572bc-b22f-4449-bde3-c2f96ee52bc6
-- title:
--   Ternary Cover High Moment: raw high moment
-- statement:
--   The Ternary Cover High Moment construction uses the raw high moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHighMoment.lean#L106-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHighMoment.lean#L106-L152

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

theorem ThreeSum.TernaryCoverHighMoment.raw_high_moment (left right : E → σ → Fin 3)
    (hinj : Function.Injective (fun e => (castWord (K := K) (left e), castWord (K := K) (right e))))
    (hE : Fintype.card E ≤ Fintype.card K ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : σ → K,
      (projectionFiber (fun e => castWord (K := K) (left e))
        (fun e => castWord (K := K) (right e)) β γ q).card ≤ Fintype.card K)
    (k : ℕ) (a b : K) :
    (∑ w, HashFamily.incidenceCount (rawEvents left right a b) w ^ k) ≤
      3 ^ (4*k^2) * Fintype.card (σ → K) := by sorry
