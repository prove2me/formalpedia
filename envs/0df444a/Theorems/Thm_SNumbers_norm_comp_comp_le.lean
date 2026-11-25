-- Prove2me | Theorems.Thm_SNumbers_norm_comp_comp_le
-- name    : SNumbers.norm_comp_comp_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:18:29.354943+00:00
-- url     : https://prove2.me/theorems/a2b1c8ad-df50-48fe-ab7a-148021391be1
-- title:
--   SNumbers: norm comp comp le
-- statement:
--   `‖B ∘ S ∘ A‖ ≤ ‖B‖ ‖S‖ ‖A‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L93-L101
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L93-L101

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.norm_comp_comp_le {W' X' Y' Z' : Type*}
    [NormedAddCommGroup W'] [NormedSpace 𝕜 W'] [NormedAddCommGroup X'] [NormedSpace 𝕜 X']
    [NormedAddCommGroup Y'] [NormedSpace 𝕜 Y'] [NormedAddCommGroup Z'] [NormedSpace 𝕜 Z']
    (A : W' →L[𝕜] X') (S : X' →L[𝕜] Y') (B : Y' →L[𝕜] Z') :
    ‖B.comp (S.comp A)‖ ≤ ‖B‖ * ‖S‖ * ‖A‖ := by sorry
