-- Prove2me | Theorems.Thm_SNumbers_norm_apply_le_deviationFromRestriction_mul
-- name    : SNumbers.norm_apply_le_deviationFromRestriction_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:24:03.17929+00:00
-- url     : https://prove2.me/theorems/65cc151e-a520-4d2f-8606-5f5fcba03d15
-- title:
--   SNumbers: norm apply le deviation From Restriction mul
-- statement:
--   Pointwise form of the restriction norm: for `x ∈ M`, `‖S x‖ ≤ ‖S|_M‖ · ‖x‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L236-L238
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L236-L238

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

theorem SNumbers.norm_apply_le_deviationFromRestriction_mul (S : X →L[𝕜] Y) {M : Submodule 𝕜 X}
    {x : X} (hx : x ∈ M) : ‖S x‖ ≤ deviationFromRestriction S M * ‖x‖ := by sorry
