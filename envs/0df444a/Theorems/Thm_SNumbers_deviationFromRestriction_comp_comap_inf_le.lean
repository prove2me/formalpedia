-- Prove2me | Theorems.Thm_SNumbers_deviationFromRestriction_comp_comap_inf_le
-- name    : SNumbers.deviationFromRestriction_comp_comap_inf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:03:27.179904+00:00
-- url     : https://prove2.me/theorems/1b290964-e01b-43ea-9cbe-ac35ed73c573
-- title:
--   SNumbers: deviation From Restriction comp comap inf le
-- statement:
--   Per-subspace multiplicativity: for `T : X → Y`, `S : Y → Z`, `M ⊆ Y` and `N ⊆ X`,
--   `‖(S ∘ T)|_{T⁻¹(M) ⊓ N}‖ ≤ ‖S|_M‖ · ‖T|_N‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L292-L310
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L292-L310

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

theorem SNumbers.deviationFromRestriction_comp_comap_inf_le (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y)
    (M : Submodule 𝕜 Y) (N : Submodule 𝕜 X) :
    deviationFromRestriction (S.comp T) (M.comap (T : X →ₗ[𝕜] Y) ⊓ N) ≤
      deviationFromRestriction S M * deviationFromRestriction T N := by sorry
