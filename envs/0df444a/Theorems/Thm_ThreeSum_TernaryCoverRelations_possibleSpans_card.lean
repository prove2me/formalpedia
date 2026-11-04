-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRelations_possibleSpans_card
-- name    : ThreeSum.TernaryCoverRelations.possibleSpans_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:43:02.611766+00:00
-- url     : https://prove2.me/theorems/ae939e9a-e99a-44fe-b5f3-dc8bbcc8e451
-- title:
--   Ternary Cover Relations: possible Spans card
-- statement:
--   The Ternary Cover Relations construction uses the possible Spans card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRelations.lean#L38-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRelations.lean#L38-L42

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRelations
open Finset
variable {K : Type*} [Field K]

theorem ThreeSum.TernaryCoverRelations.possibleSpans_card (d : ℕ) : (possibleSpans K d).card ≤ 3 ^ (d * d) := by sorry
