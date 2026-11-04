-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_admissible_event_bound
-- name    : ThreeSum.TernaryOriginalRowMenu.admissible_event_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:11.754207+00:00
-- url     : https://prove2.me/theorems/cae1e6ec-095d-4c31-a703-d0c4dee2c5dc
-- title:
--   Ternary Original Row Menu: admissible event bound
-- statement:
--   The Ternary Original Row Menu construction uses the admissible event bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L258-L269
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean#L258-L269

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

theorem ThreeSum.TernaryOriginalRowMenu.admissible_event_bound {Λ t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤) (hp : 3 ≤ Fintype.card K)
    (v : Fin t → Fin Λ → K) (hv : LinearIndependent K v) (target : Fin t → K)
    (hsize1 : 8*Λ*Fintype.card K ^ 2 ≤ Fintype.card E)
    (hsize : 8*Λ*Fintype.card K ^ (2*t) ≤ Fintype.card E) :
    Fintype.card K ^ t * ((admissible Λ ℓ V) ∩ menuEvent ℓ v target).card ≤
      3 * (admissible Λ ℓ V).card := by sorry
