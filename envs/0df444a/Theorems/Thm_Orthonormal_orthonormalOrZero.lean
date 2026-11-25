-- Prove2me | Theorems.Thm_Orthonormal_orthonormalOrZero
-- name    : Orthonormal.orthonormalOrZero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:19:02.431836+00:00
-- url     : https://prove2.me/theorems/c8f17de1-04ba-4902-8a8d-2f4209fee612
-- title:
--   Orthonormal: orthonormal Or Zero
-- statement:
--   `Orthonormal` families are `OrthonormalOrZero`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L85-L88
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L85-L88

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

theorem Orthonormal.orthonormalOrZero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {ι : Type*} {u : ι → H} (hu : Orthonormal 𝕜 u) :
    OrthonormalOrZero 𝕜 u := by sorry
