-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_admissible_at_least_half
-- name    : ThreeSum.TernaryOriginalRowMenu.admissible_at_least_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:13.591979+00:00
-- url     : https://prove2.me/theorems/ee5539dc-6bb6-468e-ac29-e4678eeb2b80
-- title:
--   Ternary Original Row Menu: admissible at least half
-- statement:
--   The Ternary Original Row Menu construction uses the admissible at least half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L232-L256
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L232-L256

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

theorem ThreeSum.TernaryOriginalRowMenu.admissible_at_least_half (Λ : ℕ) (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤)
    (hp : 3 ≤ Fintype.card K)
    (hsize : 8*Λ*Fintype.card K ^ 2 ≤ Fintype.card E) :
    Fintype.card E ^ 2 ≤ 2*(admissible Λ ℓ V).card := by sorry
