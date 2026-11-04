-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalCollisions_sum_nextCollisions_bound
-- name    : ThreeSum.TernaryOriginalCollisions.sum_nextCollisions_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:20:46.918329+00:00
-- url     : https://prove2.me/theorems/f7ddeb3c-5d57-40d0-b203-f64af8661dbe
-- title:
--   Ternary Original Collisions: sum next Collisions bound
-- statement:
--   The Ternary Original Collisions construction uses the sum next Collisions bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalCollisions.lean#L47-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalCollisions.lean#L47-L80

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalCollisions
open Finset TernaryOriginalRowMenu
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E B W : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Field E] [Algebra K E] [Fintype E] [DecidableEq E]
  [Fintype B] [DecidableEq B] [DecidableEq W]

theorem ThreeSum.TernaryOriginalCollisions.sum_nextCollisions_bound {Λ : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : B → Fin Λ → K) (hv : Function.Injective v) (hash : B → W)
    (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤) (hp : 3 ≤ Fintype.card K)
    (hsize : 8*Λ*Fintype.card K^2 ≤ Fintype.card E) :
    Fintype.card K * (∑ seed ∈ admissible Λ ℓ V, nextCollisions ℓ v hash seed) ≤
      3*(admissible Λ ℓ V).card*(collisionPairs hash).card := by sorry
