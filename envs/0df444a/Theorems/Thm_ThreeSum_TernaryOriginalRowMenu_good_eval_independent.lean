-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_good_eval_independent
-- name    : ThreeSum.TernaryOriginalRowMenu.good_eval_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:08:57.986427+00:00
-- url     : https://prove2.me/theorems/9d6d7809-0d42-4c97-a483-e196bc344dd2
-- title:
--   Ternary Original Row Menu: good eval independent
-- statement:
--   The Ternary Original Row Menu construction uses the good eval independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L121-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L121-L135

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

theorem ThreeSum.TernaryOriginalRowMenu.good_eval_independent {Λ t : ℕ} (v : Fin t → Fin Λ → K)
    (x : E) (hx : x ∉ badSeeds (E := E) v) :
    LinearIndependent K (fun i => evalVector Λ x (v i)) := by sorry
