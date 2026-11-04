-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverUniformRank_prescribedEvent_rank_bound
-- name    : ThreeSum.TernaryCoverUniformRank.prescribedEvent_rank_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:02.618512+00:00
-- url     : https://prove2.me/theorems/c31b15aa-8733-427e-8baa-8c293c91ab13
-- title:
--   Ternary Cover Uniform Rank: prescribed Event rank bound
-- statement:
--   The Ternary Cover Uniform Rank construction uses the prescribed Event rank bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverUniformRank.lean#L67-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverUniformRank.lean#L67-L91

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverUniformRank
open Finset TernaryCoverRelations
open scoped BigOperators
variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
variable [Fintype K] [DecidableEq K]

theorem ThreeSum.TernaryCoverUniformRank.prescribedEvent_rank_bound {d : ℕ} (v : Fin d → σ → K) (target : Fin d → K) :
    Fintype.card K ^ Module.finrank K (columnSpan v) * (prescribedEvent v target).card ≤
      Fintype.card (σ → K) := by sorry
