-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_menuEvent_nine_eighths
-- name    : ThreeSum.TernaryOriginalRowMenu.menuEvent_nine_eighths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:10.159915+00:00
-- url     : https://prove2.me/theorems/b6b6bfa9-96e0-4e57-a088-aaa0e2279947
-- title:
--   Ternary Original Row Menu: menu Event nine eighths
-- statement:
--   With `|E| ≥ 8 Λ p^(2t)`, every rank-`t` prescribed event occupies
--   at most `9/(8 p^t)` of the literal seed menu.  All quantities are exact
--   natural cardinalities, so no probability oracle occurs.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L185-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L185-L201

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

theorem ThreeSum.TernaryOriginalRowMenu.menuEvent_nine_eighths {Λ t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : Fin t → Fin Λ → K) (hv : LinearIndependent K v) (target : Fin t → K)
    (hsize : 8 * Λ * Fintype.card K ^ (2*t) ≤ Fintype.card E) :
    8 * Fintype.card K ^ t * (menuEvent ℓ v target).card ≤ 9 * Fintype.card E ^ 2 := by sorry
