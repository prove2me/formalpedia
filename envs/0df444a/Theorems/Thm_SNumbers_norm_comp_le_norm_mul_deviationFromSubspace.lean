-- Prove2me | Theorems.Thm_SNumbers_norm_comp_le_norm_mul_deviationFromSubspace
-- name    : SNumbers.norm_comp_le_norm_mul_deviationFromSubspace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:29:52.221074+00:00
-- url     : https://prove2.me/theorems/b63f7570-3cc9-5534-a770-e520edecd845
-- title:
--   SNumbers: norm comp le norm mul deviation From Subspace
-- statement:
--   If an operator `R : Y →L[𝕜] Y` vanishes on `V` (i.e. `V ≤ ker R`),
--   then pre-composing with `S` is controlled by the quotient norm
--   `‖π_V ∘ S‖`: `‖R ∘ S‖ ≤ ‖R‖·‖π_V ∘ S‖`. This is the elementary estimate
--   behind the Kolmogorov half: `R` factors through `Y ⧸ V` via the universal
--   lift `V.liftQL`. (`deviationFromSubspace S V = ‖π_V ∘ S‖`.)
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L415-L429
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L415-L429

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

theorem SNumbers.norm_comp_le_norm_mul_deviationFromSubspace {S : X →L[𝕜] Y}
    {V : Submodule 𝕜 Y} {R : Y →L[𝕜] Y}
    (hR : V ≤ LinearMap.ker (R : Y →ₗ[𝕜] Y)) :
    ‖R.comp S‖ ≤ ‖R‖ * deviationFromSubspace S V := by sorry
