-- Prove2me | Theorems.Thm_SNumbers_deviationFromSubspace_comp_comp_map_le
-- name    : SNumbers.deviationFromSubspace_comp_comp_map_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:01:10.979286+00:00
-- url     : https://prove2.me/theorems/4c1247aa-cb14-4b73-bc1c-5e7a68b773b8
-- title:
--   SNumbers: deviation From Subspace comp comp map le
-- statement:
--   Per-subspace (S3) bound:
--   `deviation(B ∘ S ∘ A, B(V)) ≤ ‖B‖ * ‖A‖ * deviation(S, V)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L407-L458
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L407-L458

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

theorem SNumbers.deviationFromSubspace_comp_comp_map_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (B.comp (S.comp A)) (V.map (B : Y →ₗ[𝕜] Z))
      ≤ ‖B‖ * ‖A‖ * deviationFromSubspace S V := by sorry
