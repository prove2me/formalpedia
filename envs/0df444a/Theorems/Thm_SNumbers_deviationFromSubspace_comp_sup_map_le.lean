-- Prove2me | Theorems.Thm_SNumbers_deviationFromSubspace_comp_sup_map_le
-- name    : SNumbers.deviationFromSubspace_comp_sup_map_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:09:08.955973+00:00
-- url     : https://prove2.me/theorems/24f38ffd-d5c5-4faf-ae3d-dc99bfd022f5
-- title:
--   SNumbers: deviation From Subspace comp sup map le
-- statement:
--   Per-subspace multiplicativity: for `T : X → Y`, `S : Y → Z`, `V ⊆ Z` and `U ⊆ Y`,
--   `‖π_{V ⊔ S(U)} ∘ S ∘ T‖ ≤ ‖π_V ∘ S‖ · ‖π_U ∘ T‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L282-L305
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L282-L305

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

theorem SNumbers.deviationFromSubspace_comp_sup_map_le (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y)
    (V : Submodule 𝕜 Z) (U : Submodule 𝕜 Y) :
    deviationFromSubspace (S.comp T) (V ⊔ U.map (S : Y →ₗ[𝕜] Z)) ≤
      deviationFromSubspace S V * deviationFromSubspace T U := by sorry
