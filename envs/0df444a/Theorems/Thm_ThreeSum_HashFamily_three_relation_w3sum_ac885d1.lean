-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_three_relation_w3sum_ac885d1
-- name    : ThreeSum.HashFamily.three_relation_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:27.854554+00:00
-- url     : https://prove2.me/theorems/00e3550b-56af-48c3-928e-fad2c048c599
-- title:
--   Hash Family: three relation
-- statement:
--   Any three pairwise distinct binary one-hot words are independent.
--   At a coordinate separating the first two words, the third agrees with one
--   of them, leaving one coefficient isolated.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L53-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L53-L68

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
variable [Ring K]

theorem ThreeSum.HashFamily.three_relation_w3sum_ac885d1 {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) {a b c : K}
    (h : ∀ p, a * oneHot s p + b * oneHot t p + c * oneHot u p = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by sorry
