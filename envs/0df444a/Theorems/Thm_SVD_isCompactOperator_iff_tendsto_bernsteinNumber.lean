-- Prove2me | Theorems.Thm_SVD_isCompactOperator_iff_tendsto_bernsteinNumber
-- name    : SVD.isCompactOperator_iff_tendsto_bernsteinNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:24:49.970324+00:00
-- url     : https://prove2.me/theorems/f185fe7d-a193-44d7-aced-dabad31a9b5d
-- title:
--   SVD: is Compact Operator iff tendsto bernstein Number
-- statement:
--   Hilbert-space case: compactness is equivalent to `bₙ(S) → 0`. On a general
--   Banach space only the forward implication holds.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L460-L462
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L460-L462

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
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

theorem SVD.isCompactOperator_iff_tendsto_bernsteinNumber (S : H₁ →L[𝕜] H₂) :
    IsCompactOperator S ↔ Tendsto (SNumbers.bernsteinNumber S) atTop (𝓝 0) := by sorry
