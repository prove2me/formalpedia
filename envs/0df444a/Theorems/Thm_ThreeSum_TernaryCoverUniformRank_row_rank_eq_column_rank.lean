-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverUniformRank_row_rank_eq_column_rank
-- name    : ThreeSum.TernaryCoverUniformRank.row_rank_eq_column_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:03.382718+00:00
-- url     : https://prove2.me/theorems/be646fd7-3821-494c-b2c6-1c33729b553f
-- title:
--   Ternary Cover Uniform Rank: row rank eq column rank
-- statement:
--   The Ternary Cover Uniform Rank construction uses the row rank eq column rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverUniformRank.lean#L48-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverUniformRank.lean#L48-L60

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

theorem ThreeSum.TernaryCoverUniformRank.row_rank_eq_column_rank {d : ℕ} (v : Fin d → σ → K) :
    Module.finrank K (Submodule.span K (Set.range v)) = Module.finrank K (columnSpan v) := by sorry
