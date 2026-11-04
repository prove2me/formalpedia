-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRelations_paired_possibleSpans_card
-- name    : ThreeSum.TernaryCoverRelations.paired_possibleSpans_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:43:15.165516+00:00
-- url     : https://prove2.me/theorems/d4133fe6-05ac-4499-a1b1-fbb129e27b34
-- title:
--   Ternary Cover Relations: paired possible Spans card
-- statement:
--   For `2k` paired rows, the number of actual relation spans has the
--   subquadratic-in-the-parameter exponent used in the high moment audit.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRelations.lean#L91-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRelations.lean#L91-L93

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

theorem ThreeSum.TernaryCoverRelations.paired_possibleSpans_card (k : ℕ) :
    (possibleSpans K (2 * k)).card ≤ 3 ^ (4 * k ^ 2) := by sorry
