-- Prove2me | Theorems.Thm_SNumbers_L2Linf_sum_sum_norm_sq_apply
-- name    : SNumbers.L2Linf.sum_sum_norm_sq_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:59:37.596943+00:00
-- url     : https://prove2.me/theorems/576daaaa-3558-4a91-8cbb-145c6611ada1
-- title:
--   L2 Linf: sum sum norm sq apply
-- statement:
--   The coordinates of an orthonormal basis of `M ⊆ ℓ₂ᴺ` carry total mass `dim M`:
--   `∑ₖ ∑ᵢ |vᵢ(k)|² = ∑ᵢ ‖vᵢ‖₂² = |ι|`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L130-L136
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L130-L136

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
variable {N : ℕ} {ι : Type*} [Fintype ι] {M : Submodule 𝕜 (PiLp 2 (fun _ : Fin N => 𝕜))}

theorem SNumbers.L2Linf.sum_sum_norm_sq_apply (b : OrthonormalBasis ι 𝕜 M) :
    ∑ k, ∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 = Fintype.card ι := by sorry
