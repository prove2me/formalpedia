-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_vectorPoly_injective
-- name    : ThreeSum.TernaryOriginalRowMenu.vectorPoly_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:08:57.588225+00:00
-- url     : https://prove2.me/theorems/76c9883e-454d-47e6-bd5a-2fc29402dbff
-- title:
--   Ternary Original Row Menu: vector Poly injective
-- statement:
--   The Ternary Original Row Menu construction uses the vector Poly injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L25-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L25-L29

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

theorem ThreeSum.TernaryOriginalRowMenu.vectorPoly_injective (Λ : ℕ) : Function.Injective (vectorPoly (K := K) (E := E) Λ) := by sorry
