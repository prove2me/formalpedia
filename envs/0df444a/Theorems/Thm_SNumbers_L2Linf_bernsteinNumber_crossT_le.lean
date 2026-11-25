-- Prove2me | Theorems.Thm_SNumbers_L2Linf_bernsteinNumber_crossT_le
-- name    : SNumbers.L2Linf.bernsteinNumber_crossT_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:00:27.095333+00:00
-- url     : https://prove2.me/theorems/eb187211-2c6d-4b70-a6d2-57c1a984cd3d
-- title:
--   L2 Linf: bernstein Number cross T le
-- statement:
--   `b₃₅(T) ≤ √(71/36)/9`, from `b₃₅(id : ℓ∞⁷¹ → ℓ₂⁷¹) ≤ √(71/36)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L320-L346
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L320-L346

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
open SNumbers SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]

theorem SNumbers.L2Linf.bernsteinNumber_crossT_le :
    bernsteinNumber (crossT (𝕜 := 𝕜)) 35 ≤ Real.sqrt (71 / 36) / 9 := by sorry
