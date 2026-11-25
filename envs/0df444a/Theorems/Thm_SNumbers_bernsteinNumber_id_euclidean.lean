-- Prove2me | Theorems.Thm_SNumbers_bernsteinNumber_id_euclidean
-- name    : SNumbers.bernsteinNumber_id_euclidean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:14:42.328256+00:00
-- url     : https://prove2.me/theorems/9cc4b98e-a989-5f2a-9783-97f4d528034c
-- title:
--   SNumbers: bernstein Number id euclidean
-- statement:
--   (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5').
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L343-L348
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L343-L348

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
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

theorem SNumbers.bernsteinNumber_id_euclidean (n : ℕ) :
    bernsteinNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by sorry
