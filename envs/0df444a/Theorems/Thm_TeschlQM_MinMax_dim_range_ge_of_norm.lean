-- Prove2me | Theorems.Thm_TeschlQM_MinMax_dim_range_ge_of_norm
-- name    : TeschlQM.MinMax.dim_range_ge_of_norm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:37:06.465143+00:00
-- url     : https://prove2.me/theorems/545004d3-08f8-4fbe-be88-25c8fc07a905
-- title:
--   Theorem 4.12 (ii) — ‖(A − (λ₂+λ₁)/2)ψ‖ < ((λ₂−λ₁)/2)‖ψ‖ on a k-dimensional span forces dim Ran P_A((λ₁, λ₂)) ≥ k
-- statement:
--   Let $A$ be a self-adjoint operator on a complex Hilbert space $\mathfrak H$ with projection-valued measure $P_A$, let $\lambda_1 < \lambda_2$, and let $\psi_1, \dots, \psi_k \in \mathfrak D(A)$ be linearly independent. If
--   $$\Big\| \Big(A - \frac{\lambda_2 + \lambda_1}{2}\Big)\psi \Big\| < \frac{\lambda_2 - \lambda_1}{2} \|\psi\|$$
--   for every nonzero linear combination $\psi = \sum_{j=1}^k c_j \psi_j$, then
--   $$\dim \operatorname{Ran} P_A((\lambda_1, \lambda_2)) \ge k .$$
--
--   Approximate eigenvectors whose residual is small compared with the half-width of the interval thus certify spectral subspace of at least the corresponding dimension inside the interval.
--
--   **Formalization Note.** As in part (i), the projection-valued measure $P$ is taken as data with the hypothesis $A = \int \lambda\, dP(\lambda)$, so $P_A = P$. The vectors $\psi_j$ are elements of `A.domain` and the linear combinations are formed there. Dimensions are cardinals (`Module.rank`).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 119, Theorem 4.12 (ii)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral

namespace TeschlQM.MinMax

/-- Teschl, Theorem 4.12 (ii), p. 119, (4.35)–(4.36): let `A` be self-adjoint with
projection-valued measure `P` (i.e. `A = ∫ λ dP(λ)`, so `P_A = P`), let `λ₁ < λ₂` and let
`ψ₁, …, ψ_k ∈ 𝔇(A)` be linearly independent. If
`‖(A − (λ₂ + λ₁)/2)ψ‖ < ((λ₂ − λ₁)/2)‖ψ‖` for every nonzero linear combination `ψ` of the `ψ_j`,
then `dim Ran P_A((λ₁, λ₂)) ≥ k`. Dimensions are cardinals (`Module.rank`). -/
theorem dim_range_ge_of_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    (lam₁ lam₂ : ℝ) (hlt : lam₁ < lam₂)
    {k : ℕ} (ψ : Fin k → A.domain) (hli : LinearIndependent ℂ (fun j => (ψ j : H)))
    (h : ∀ φ ∈ Submodule.span ℂ (Set.range ψ), φ ≠ 0 →
      ‖A φ - (((lam₂ + lam₁) / 2 : ℝ) : ℂ) • (φ : H)‖ < (lam₂ - lam₁) / 2 * ‖(φ : H)‖) :
    (k : Cardinal) ≤ Module.rank ℂ (LinearMap.range (P (Set.Ioo lam₁ lam₂) : H →ₗ[ℂ] H)) := by sorry

end TeschlQM.MinMax
