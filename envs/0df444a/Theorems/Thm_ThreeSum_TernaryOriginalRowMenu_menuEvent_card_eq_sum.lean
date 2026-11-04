-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_menuEvent_card_eq_sum
-- name    : ThreeSum.TernaryOriginalRowMenu.menuEvent_card_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:07.467541+00:00
-- url     : https://prove2.me/theorems/b89b3e21-ad51-4cde-a969-1ef14cfe55cf
-- title:
--   Ternary Original Row Menu: menu Event card eq sum
-- statement:
--   The Ternary Original Row Menu construction uses the menu Event card eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L144-L155
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L144-L155

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

theorem ThreeSum.TernaryOriginalRowMenu.menuEvent_card_eq_sum {Λ t : ℕ} (ℓ : E →ₗ[K] K)
    (v : Fin t → Fin Λ → K) (target : Fin t → K) :
    (menuEvent ℓ v target).card = ∑ x : E,
      (univ.filter fun y : E => jointMap ℓ (fun i => evalVector Λ x (v i)) y = target).card := by sorry
