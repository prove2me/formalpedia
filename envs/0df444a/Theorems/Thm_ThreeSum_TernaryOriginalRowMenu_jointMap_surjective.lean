-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_jointMap_surjective
-- name    : ThreeSum.TernaryOriginalRowMenu.jointMap_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:08:58.914194+00:00
-- url     : https://prove2.me/theorems/920f6637-bfd4-4ea4-a854-00c8348053b2
-- title:
--   Ternary Original Row Menu: joint Map surjective
-- statement:
--   The Ternary Original Row Menu construction uses the joint Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L64-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L64-L76

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

theorem ThreeSum.TernaryOriginalRowMenu.jointMap_surjective {t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : Fin t → E) (hv : LinearIndependent K v) :
    Function.Surjective (jointMap ℓ v) := by sorry
