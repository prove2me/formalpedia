-- Prove2me | Theorems.Thm_SNumbers_norm_det_le_detNumber
-- name    : SNumbers.norm_det_le_detNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:37:12.530449+00:00
-- url     : https://prove2.me/theorems/73a51405-4b25-460d-b071-9ed908ce8d21
-- title:
--   SNumbers: norm det le det Number
-- statement:
--   Every admissible pair bounds `Δₖ(S)` from below.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L202-L207
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L202-L207

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

theorem SNumbers.norm_det_le_detNumber (S : X →L[𝕜] Y) {k : ℕ}
    {A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X} {B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖LinearMap.det (B.comp (S.comp A) :
        EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖ ≤ detNumber S k := by sorry
