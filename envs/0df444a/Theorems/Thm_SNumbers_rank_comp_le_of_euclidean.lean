-- Prove2me | Theorems.Thm_SNumbers_rank_comp_le_of_euclidean
-- name    : SNumbers.rank_comp_le_of_euclidean
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:37:45.746711+00:00
-- url     : https://prove2.me/theorems/29a82edd-2374-4862-9a7c-e7cd0957c71c
-- title:
--   SNumbers: rank comp le of euclidean
-- statement:
--   An operator that factors through the `k`-dimensional space `ℓ₂ᵏ` has rank
--   at most `k`. This is what makes the approximant `L = SA(BSA)⁻¹BS` below
--   admissible for `aₖ`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L441-L449
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L441-L449

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.rank_comp_le_of_euclidean {k : ℕ} (F : EuclideanSpace 𝕜 (Fin k) →L[𝕜] Y)
    (G : X →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    (F.comp G).rank ≤ (k : Cardinal) := by sorry
