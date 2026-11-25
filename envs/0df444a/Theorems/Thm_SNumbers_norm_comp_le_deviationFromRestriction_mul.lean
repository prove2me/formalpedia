-- Prove2me | Theorems.Thm_SNumbers_norm_comp_le_deviationFromRestriction_mul
-- name    : SNumbers.norm_comp_le_deviationFromRestriction_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:28:43.827877+00:00
-- url     : https://prove2.me/theorems/25a5cdbe-228c-44d7-b539-3f04f0152abd
-- title:
--   SNumbers: norm comp le deviation From Restriction mul
-- statement:
--   If an operator `R : X →L[𝕜] X` has its whole range inside `M`, then
--   post-composing with `S` is controlled by the restricted norm `‖S|_M‖`:
--   `‖S ∘ R‖ ≤ ‖S|_M‖·‖R‖`. This is the elementary estimate behind the
--   Gelfand half. (`deviationFromRestriction S M = ‖S|_M‖`.)
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L393-L407
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L393-L407

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]
omit [CompleteSpace X] [CompleteSpace Y]

theorem SNumbers.norm_comp_le_deviationFromRestriction_mul {S : X →L[𝕜] Y}
    {M : Submodule 𝕜 X} {R : X →L[𝕜] X} (hR : ∀ x, R x ∈ M) :
    ‖S.comp R‖ ≤ deviationFromRestriction S M * ‖R‖ := by sorry
