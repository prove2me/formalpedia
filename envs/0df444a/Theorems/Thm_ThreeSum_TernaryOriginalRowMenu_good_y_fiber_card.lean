-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_good_y_fiber_card
-- name    : ThreeSum.TernaryOriginalRowMenu.good_y_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:08:59.109328+00:00
-- url     : https://prove2.me/theorems/72935259-5f3c-4c89-a665-d04261a6da37
-- title:
--   Ternary Original Row Menu: good y fiber card
-- statement:
--   The Ternary Original Row Menu construction uses the good y fiber card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L78-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L78-L83

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

theorem ThreeSum.TernaryOriginalRowMenu.good_y_fiber_card {t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : Fin t → E) (hv : LinearIndependent K v) (target : Fin t → K) :
    Fintype.card K ^ t * (univ.filter fun y => jointMap ℓ v y = target).card =
      Fintype.card E := by sorry
