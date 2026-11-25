-- Prove2me | Theorems.Thm_SVD_IsCompactOperator_diagonalFactorisation
-- name    : SVD.IsCompactOperator.diagonalFactorisation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:06:58.587373+00:00
-- url     : https://prove2.me/theorems/59a690ef-6807-46ec-86e1-24f2e4c26ad4
-- title:
--   Is Compact Operator: diagonal Factorisation
-- statement:
--   **Diagonal factorisation through `ℓ₂ⁿ⁺¹`.** There is an isometric
--   inclusion `A : ℓ₂ⁿ⁺¹ →L[𝕜] H₁` with `‖A‖ ≤ 1` and a contraction
--   `B : H₂ →L[𝕜] ℓ₂ⁿ⁺¹` with `‖B‖ ≤ 1` such that on each basis vector,
--
--   ```
--   (B ∘ S ∘ A)(eₖ) = aₖ(S) · eₖ,
--   ```
--
--   i.e. `B ∘ S ∘ A = diag(a₀(S), …, aₙ(S))`. Built from the top `n+1` singular
--   pairs only.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1206-L1289
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1206-L1289

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

theorem SVD.IsCompactOperator.diagonalFactorisation
    [Nontrivial H₁] [Nontrivial H₂]
    {S : H₁ →L[𝕜] H₂} (hS : IsCompactOperator S) (n : ℕ) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ∀ k : Fin (n + 1),
        B (S (A (EuclideanSpace.single k (1 : 𝕜)))) =
          (SNumbers.approximationNumber S k : 𝕜) •
            EuclideanSpace.single k (1 : 𝕜) := by sorry
