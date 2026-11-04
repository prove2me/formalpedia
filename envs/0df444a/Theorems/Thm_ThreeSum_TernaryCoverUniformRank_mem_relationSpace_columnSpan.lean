-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverUniformRank_mem_relationSpace_columnSpan
-- name    : ThreeSum.TernaryCoverUniformRank.mem_relationSpace_columnSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:01.685323+00:00
-- url     : https://prove2.me/theorems/d51d1ae2-c958-4cf9-99f5-35c49e696f25
-- title:
--   Ternary Cover Uniform Rank: mem relation Space column Span
-- statement:
--   The Ternary Cover Uniform Rank construction uses the mem relation Space column Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverUniformRank.lean#L23-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverUniformRank.lean#L23-L35

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

theorem ThreeSum.TernaryCoverUniformRank.mem_relationSpace_columnSpan {d : ℕ} (v : Fin d → σ → K) (a : Fin d → K) :
    a ∈ relationSpace (columnSpan v) ↔ ∀ i, ∑ j, a j * v j i = 0 := by sorry
