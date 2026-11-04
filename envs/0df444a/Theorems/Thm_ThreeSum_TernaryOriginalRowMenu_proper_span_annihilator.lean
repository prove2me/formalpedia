-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_proper_span_annihilator
-- name    : ThreeSum.TernaryOriginalRowMenu.proper_span_annihilator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:07.474134+00:00
-- url     : https://prove2.me/theorems/99b01ab5-d442-40ac-bd29-41270819df25
-- title:
--   Ternary Original Row Menu: proper span annihilator
-- statement:
--   The Ternary Original Row Menu construction uses the proper span annihilator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L215-L230
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L215-L230

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

theorem ThreeSum.TernaryOriginalRowMenu.proper_span_annihilator (Λ : ℕ) (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤) :
    ∃ v : Fin Λ → K, v ≠ 0 ∧ ∀ w ∈ V, ∑ i, v i * w i = 0 := by sorry
