-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_oneHot_four_independent
-- name    : ThreeSum.HashFamily.oneHot_four_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:28.173278+00:00
-- url     : https://prove2.me/theorems/78c7b0b5-de6f-40c7-9948-a277d6a53a1f
-- title:
--   Hash Family: one Hot four independent
-- statement:
--   The Hash Family construction uses the one Hot four independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L125-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L125-L136

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
variable [Field K]

theorem ThreeSum.HashFamily.oneHot_four_independent {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) :
    LinearIndependent K ![oneHot (K := K) s, oneHot t, oneHot u, oneHot v] := by sorry
