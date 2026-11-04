-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_badPartners_card_le_w3sum_ac885d1
-- name    : ThreeSum.HashFamily.badPartners_card_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:49.307179+00:00
-- url     : https://prove2.me/theorems/1a672a7b-7f27-427b-81fc-ccc5e19bd26a
-- title:
--   Hash Family: bad Partners card le
-- statement:
--   The Hash Family construction uses the bad Partners card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L448-L467
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L448-L467

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
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.HashFamily.badPartners_card_le_w3sum_ac885d1 (left right : E → α → Bool) (e : E) (Delta G : ℕ)
    (hL : (Finset.univ.filter (fun f => left e = left f)).card ≤ Delta)
    (hR : (Finset.univ.filter (fun f => right e = right f)).card ≤ Delta)
    (hG : (Finset.univ.filter (fun f =>
      outputMask left right e = outputMask left right f)).card ≤ G) :
    (badPartners left right e).card ≤ 2 * Delta + G := by sorry
