-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_id_euclidean
-- name    : SNumbers.gelfandNumber_id_euclidean
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:06:30.490272+00:00
-- url     : https://prove2.me/theorems/121a46bd-f15f-5f3d-9296-9ae61e77395a
-- title:
--   SNumbers: gelfand Number id euclidean
-- statement:
--   (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5').
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L522-L527
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L522-L527

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.gelfandNumber_id_euclidean (n : ℕ) :
    gelfandNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by sorry
