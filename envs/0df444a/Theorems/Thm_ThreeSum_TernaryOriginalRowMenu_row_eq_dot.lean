-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_row_eq_dot
-- name    : ThreeSum.TernaryOriginalRowMenu.row_eq_dot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:10.336109+00:00
-- url     : https://prove2.me/theorems/483d1bfa-1ae1-4e26-9c59-566d0b31b6f9
-- title:
--   Ternary Original Row Menu: row eq dot
-- statement:
--   The Ternary Original Row Menu construction uses the row eq dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L206-L210
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L206-L210

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

theorem ThreeSum.TernaryOriginalRowMenu.row_eq_dot (Λ : ℕ) (ℓ : E →ₗ[K] K) (seed : E × E) (v : Fin Λ → K) :
    row Λ ℓ seed v = ∑ i, v i * seedRow Λ ℓ seed i := by sorry
