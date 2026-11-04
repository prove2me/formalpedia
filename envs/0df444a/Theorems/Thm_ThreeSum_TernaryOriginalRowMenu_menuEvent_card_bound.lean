-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_menuEvent_card_bound
-- name    : ThreeSum.TernaryOriginalRowMenu.menuEvent_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:08.696202+00:00
-- url     : https://prove2.me/theorems/f8cd053e-27e9-44b3-aa55-5ab4f0452db0
-- title:
--   Ternary Original Row Menu: menu Event card bound
-- statement:
--   The Ternary Original Row Menu construction uses the menu Event card bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L157-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L157-L180

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

theorem ThreeSum.TernaryOriginalRowMenu.menuEvent_card_bound {Λ t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : Fin t → Fin Λ → K) (hv : LinearIndependent K v) (target : Fin t → K) :
    Fintype.card K ^ t * (menuEvent ℓ v target).card ≤
      Fintype.card E ^ 2 + Fintype.card K ^ t *
        ((Fintype.card K ^ t - 1) * (Λ - 1)) * Fintype.card E := by sorry
