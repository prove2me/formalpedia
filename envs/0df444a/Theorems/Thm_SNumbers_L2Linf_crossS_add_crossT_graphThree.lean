-- Prove2me | Theorems.Thm_SNumbers_L2Linf_crossS_add_crossT_graphThree
-- name    : SNumbers.L2Linf.crossS_add_crossT_graphThree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:00:07.135663+00:00
-- url     : https://prove2.me/theorems/7f652ddf-ffbe-5856-9c39-43368e6e5e3d
-- title:
--   L2 Linf: cross S add cross T graph Three
-- statement:
--   On the graph of `x ↦ 3x`, the operator `S + T` is multiplication by `1/3`:
--   `(S + T)(x, 3x) = (x/3, x)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L266-L274
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L266-L274

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

theorem SNumbers.L2Linf.crossS_add_crossT_graphThree (x : PiLp 2 (fun _ : Fin 71 => 𝕜)) :
    (crossS + crossT : L2LinfProd 𝕜 →L[𝕜] L2LinfProd 𝕜) (graphThree x) =
      (3 : 𝕜)⁻¹ • graphThree x := by sorry
