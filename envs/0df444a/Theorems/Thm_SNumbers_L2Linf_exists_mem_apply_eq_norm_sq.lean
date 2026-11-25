-- Prove2me | Theorems.Thm_SNumbers_L2Linf_exists_mem_apply_eq_norm_sq
-- name    : SNumbers.L2Linf.exists_mem_apply_eq_norm_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:59:27.729426+00:00
-- url     : https://prove2.me/theorems/0069755d-285b-4f70-9186-93c4017af53d
-- title:
--   L2 Linf: exists mem apply eq norm sq
-- statement:
--   For an orthonormal basis `(vᵢ)` of a subspace `M ⊆ ℓ₂ᴺ` and a coordinate `k`, the
--   vector `x = ∑ᵢ conj(vᵢ(k)) vᵢ ∈ M` satisfies `x(k) = ‖x‖₂² = ∑ᵢ |vᵢ(k)|²`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L117-L126
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L117-L126

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

theorem SNumbers.L2Linf.exists_mem_apply_eq_norm_sq (b : OrthonormalBasis ι 𝕜 M) (k : Fin N) :
    ∃ x ∈ M, x k = ((∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 : ℝ) : 𝕜) ∧
      ‖x‖ ^ 2 = ∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 := by sorry
