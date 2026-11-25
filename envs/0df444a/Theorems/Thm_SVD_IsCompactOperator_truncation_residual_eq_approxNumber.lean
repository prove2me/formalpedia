-- Prove2me | Theorems.Thm_SVD_IsCompactOperator_truncation_residual_eq_approxNumber
-- name    : SVD.IsCompactOperator.truncation_residual_eq_approxNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:19:14.247849+00:00
-- url     : https://prove2.me/theorems/3c7aceb7-cea0-4881-8900-fe9d95bfe558
-- title:
--   Is Compact Operator: truncation residual eq approx Number
-- statement:
--   **Eckart–Young.** Some rank-`n` operator `L` attains the approximation
--   number: `‖S - L‖ = aₙ(S)` (the truncated SVD). In particular the infimum
--   defining `aₙ(S)` is attained on Hilbert spaces.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1162-L1184
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1162-L1184

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

theorem SVD.IsCompactOperator.truncation_residual_eq_approxNumber
    [Nontrivial H₁] [Nontrivial H₂]
    {S : H₁ →L[𝕜] H₂} (hS : IsCompactOperator S) (n : ℕ) :
    ∃ L : H₁ →L[𝕜] H₂, L.rank ≤ (n : Cardinal) ∧
      ‖S - L‖ = SNumbers.approximationNumber S n := by sorry
