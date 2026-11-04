-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_vectorPoly_natDegree_le
-- name    : ThreeSum.TernaryOriginalRowMenu.vectorPoly_natDegree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:08:56.209411+00:00
-- url     : https://prove2.me/theorems/99323635-cbce-40c4-bf4a-0dd966da7142
-- title:
--   Ternary Original Row Menu: vector Poly nat Degree le
-- statement:
--   The Ternary Original Row Menu construction uses the vector Poly nat Degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L31-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L31-L38

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalRowMenu
open Finset
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]

theorem ThreeSum.TernaryOriginalRowMenu.vectorPoly_natDegree_le (Λ : ℕ) (v : Fin Λ → K) :
    (vectorPoly (E := E) Λ v).natDegree ≤ Λ - 1 := by sorry
