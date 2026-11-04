-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_tripleEvent_card
-- name    : ThreeSum.HashFamily.tripleEvent_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:37.959733+00:00
-- url     : https://prove2.me/theorems/7d2a0983-1c58-49da-8e94-cb13ac5d2ed1
-- title:
--   Hash Family: triple Event card
-- statement:
--   The Hash Family construction uses the triple Event card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L297-L304
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L297-L304

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.HashFamily.tripleEvent_card {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (a b c : K) :
    Fintype.card K ^ 3 * (wordEvent ![s, t, u] ![a, b, c]).card =
      Fintype.card (α × Bool → K) := by sorry
