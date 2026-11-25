-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_id_euclidean
-- name    : SNumbers.kolmogorovNumber_id_euclidean
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:30:50.814607+00:00
-- url     : https://prove2.me/theorems/a5d98818-8fe0-4ca5-8e8c-59297d0f30f6
-- title:
--   SNumbers: kolmogorov Number id euclidean
-- statement:
--   (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5').
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L549-L554
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L549-L554

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
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

theorem SNumbers.kolmogorovNumber_id_euclidean (n : ℕ) :
    kolmogorovNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by sorry
