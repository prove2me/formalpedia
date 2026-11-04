-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_oneHot_two_independent
-- name    : ThreeSum.HashFamily.oneHot_two_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:23.957471+00:00
-- url     : https://prove2.me/theorems/1b2db9f7-b928-47ae-a0bc-76675bfd6476
-- title:
--   Hash Family: one Hot two independent
-- statement:
--   The Hash Family construction uses the one Hot two independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L106-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L106-L113

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

theorem ThreeSum.HashFamily.oneHot_two_independent {s t : α → Bool} (hst : s ≠ t) :
    LinearIndependent K ![oneHot (K := K) s, oneHot t] := by sorry
