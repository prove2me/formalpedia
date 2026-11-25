-- Prove2me | Theorems.Thm_SVD_OrthonormalOrZero_orthonormal_comp
-- name    : SVD.OrthonormalOrZero.orthonormal_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:06:49.878327+00:00
-- url     : https://prove2.me/theorems/c10eb54e-ba76-4f5e-9042-0b53244a204f
-- title:
--   Orthonormal Or Zero: orthonormal comp
-- statement:
--   **Restricting away the zeros.** An `OrthonormalOrZero` family, reindexed along
--   an injective map that only hits unit vectors, is `Orthonormal`. This is how a
--   finite subfamily of an SVD family (the indices with non-zero singular value) is
--   recognised as an orthonormal basis of its span.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L104-L114
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L104-L114

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_BasicResults_Spectral_Representation
public import Definitions.Def_BasicResults_SVD
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal
open SVD
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

theorem SVD.OrthonormalOrZero.orthonormal_comp {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : ι → H}
    (h : OrthonormalOrZero 𝕜 u) {g : κ → ι} (hg : Function.Injective g)
    (hn : ∀ k, ‖u (g k)‖ = 1) :
    Orthonormal 𝕜 (fun k => u (g k)) := by sorry
