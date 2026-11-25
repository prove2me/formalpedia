-- Prove2me | Theorems.Thm_SVD_mul_approximationNumber_le_of_factorization
-- name    : SVD.mul_approximationNumber_le_of_factorization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:12:19.839782+00:00
-- url     : https://prove2.me/theorems/a170d4a5-4882-4dff-ae66-847abb54e649
-- title:
--   SVD: mul approximation Number le of factorization
-- statement:
--   **`(n+1)·aₙ(T) ≤ ‖T₁‖_HS·‖T₂‖_HS` for a factored compact operator.**
--
--   Let `T = T₂T₁` be compact, and suppose that along every orthonormal-or-zero
--   family the two factors satisfy the Hilbert–Schmidt bounds
--   `∑ₖ ‖T₁ uₖ‖² ≤ a²` and `∑ₖ ‖T₂* vₖ‖² ≤ b²`. Then
--   `(n+1)·aₙ(T) ≤ ∑_{k≤n} σₖ(T) ≤ b·a` for every `n`.
--
--   The first inequality is antitonicity of the singular values, the second is
--   `svd_sigma_le_mul_of_factorization` followed by Cauchy–Schwarz and the two
--   hypotheses.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1506-L1539
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1506-L1539

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
variable {H₃ : Type u}
variable [NormedAddCommGroup H₃] [InnerProductSpace 𝕜 H₃] [CompleteSpace H₃]

theorem SVD.mul_approximationNumber_le_of_factorization {T : H₁ →L[𝕜] H₃}
    (hT : IsCompactOperator T) {T₁ : H₁ →L[𝕜] H₂} {T₂ : H₂ →L[𝕜] H₃}
    (hfact : T = T₂.comp T₁) {a b : ℝ}
    (ha : ∀ u : ℕ → H₁, OrthonormalOrZero 𝕜 u → ∀ s : Finset ℕ,
      ∑ k ∈ s, ‖T₁ (u k)‖ ^ 2 ≤ a ^ 2)
    (hb : ∀ v : ℕ → H₃, OrthonormalOrZero 𝕜 v → ∀ s : Finset ℕ,
      ∑ k ∈ s, ‖ContinuousLinearMap.adjoint T₂ (v k)‖ ^ 2 ≤ b ^ 2)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (n : ℕ) :
    ((n : ℝ) + 1) * SNumbers.approximationNumber T n ≤ b * a := by sorry
