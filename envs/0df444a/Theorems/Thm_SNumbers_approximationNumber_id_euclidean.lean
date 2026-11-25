-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_id_euclidean
-- name    : SNumbers.approximationNumber_id_euclidean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:39.717535+00:00
-- url     : https://prove2.me/theorems/8a8a0507-26e2-4ed7-9971-d0ffb52abd51
-- title:
--   SNumbers: approximation Number id euclidean
-- statement:
--   (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5').
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L377-L382
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L377-L382

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
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
variable [CompleteSpace 𝕜]

theorem SNumbers.approximationNumber_id_euclidean (n : ℕ) :
    approximationNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by sorry
