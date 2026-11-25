-- Prove2me | Theorems.Thm_SVD_exists_scalar_factorisation
-- name    : SVD.exists_scalar_factorisation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:04:06.214638+00:00
-- url     : https://prove2.me/theorems/1bc67da9-34f4-524b-9761-93df7e34c799
-- title:
--   SVD: exists scalar factorisation
-- statement:
--   **Scalar factorisation.** For any bounded `S : H₁ →L[𝕜] H₂` between
--   Hilbert spaces and any real `c` with `0 ≤ c < aₙ(S)`, there are contractions
--   `A : ℓ₂ⁿ⁺¹ →L[𝕜] H₁`, `B : H₂ →L[𝕜] ℓ₂ⁿ⁺¹` with
--
--   ```
--   B ∘ S ∘ A = c • id_{ℓ₂ⁿ⁺¹}.
--   ```
--
--   **Proved** from `SpectralRepresentation.exists_lowerBound_subspace`: take an
--   orthonormal basis of the lower-bound subspace `M` for `A`, set `T := S ∘ A`
--   (bounded below by `c`), and `B := c · (T*T)⁻¹ ∘ T*` (well-defined since `T*T`
--   is a unit, via `isUnit_of_forall_le_norm_inner_map`). No compactness needed.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1319-L1389
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1319-L1389

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

theorem SVD.exists_scalar_factorisation
    (S : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c < SNumbers.approximationNumber S n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      B.comp (S.comp A) =
        (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by sorry
