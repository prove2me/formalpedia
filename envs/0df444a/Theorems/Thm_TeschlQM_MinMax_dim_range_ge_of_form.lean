-- Prove2me | Theorems.Thm_TeschlQM_MinMax_dim_range_ge_of_form
-- name    : TeschlQM.MinMax.dim_range_ge_of_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T21:33:33.603664+00:00
-- url     : https://prove2.me/theorems/ff7b853a-19c8-4cb8-9c41-65fdbf8e6e2a
-- title:
--   Theorem 4.12 (i) — ⟨ψ, Aψ⟩ < λ‖ψ‖² on a k-dimensional span forces dim Ran P_A((−∞, λ)) ≥ k
-- statement:
--   Let $A$ be a self-adjoint operator on a complex Hilbert space $\mathfrak H$ with projection-valued measure $P_A$ and form domain $\mathfrak Q(A)$, and let $\psi_1, \dots, \psi_k \in \mathfrak Q(A)$ be linearly independent. Let $\lambda \in \mathbb R$. If
--   $$\langle \psi, A\psi \rangle < \lambda \|\psi\|^2$$
--   for every nonzero linear combination $\psi = \sum_{j=1}^k c_j \psi_j$, then
--   $$\dim \operatorname{Ran} P_A((-\infty, \lambda)) \ge k .$$
--   Similarly, if $\langle \psi, A\psi \rangle > \lambda\|\psi\|^2$ for every such $\psi$, then $\dim \operatorname{Ran} P_A((\lambda, \infty)) \ge k$.
--
--   A $k$-dimensional space of trial functions on which the expectation of $A$ stays below $\lambda$ thus certifies at least $k$ dimensions of spectral subspace below $\lambda$.
--
--   **Formalization Note.** The spectral theorem is not formalized here: the projection-valued measure $P$ is taken as data with the hypothesis that $A = \int \lambda\, dP(\lambda)$ (`IsSpectralIntegral P (fun x => x) A`), so $P_A = P$. For $\psi \in \mathfrak Q(A)$, $\langle\psi, A\psi\rangle$ is the quadratic form $q_A(\psi) = \int \eta \, d\mu_\psi(\eta)$ (`quadForm P ψ`). Dimensions are cardinals (`Module.rank`), so an infinite-dimensional range satisfies the bound. The Hilbert space is not assumed separable.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 119, Theorem 4.12 (i)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
import Definitions.Def_TeschlQM_MinMax_formDomain

namespace TeschlQM.MinMax

/-- Teschl, Theorem 4.12 (i), p. 119, (4.33)–(4.34): let `A` be self-adjoint with
projection-valued measure `P` (i.e. `A = ∫ λ dP(λ)`, so `P_A = P`), let `ψ₁, …, ψ_k` be linearly
independent elements of the form domain `𝔔(A)` and `λ ∈ ℝ`. If `⟨ψ, Aψ⟩ < λ‖ψ‖²` (the quadratic
form `q_A(ψ) = ∫ η dμ_ψ(η)`) for every nonzero linear combination `ψ` of the `ψ_j`, then
`dim Ran P_A((−∞, λ)) ≥ k`; similarly `⟨ψ, Aψ⟩ > λ‖ψ‖²` implies `dim Ran P_A((λ, ∞)) ≥ k`.
Dimensions are cardinals (`Module.rank`). -/
theorem dim_range_ge_of_form {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    {k : ℕ} (ψ : Fin k → H) (hli : LinearIndependent ℂ ψ) (hQ : ∀ j, ψ j ∈ formDomain P)
    (lam : ℝ) :
    ((∀ φ ∈ Submodule.span ℂ (Set.range ψ), φ ≠ 0 → quadForm P φ < lam * ‖φ‖ ^ 2) →
        (k : Cardinal) ≤ Module.rank ℂ (LinearMap.range (P (Set.Iio lam) : H →ₗ[ℂ] H))) ∧
      ((∀ φ ∈ Submodule.span ℂ (Set.range ψ), φ ≠ 0 → lam * ‖φ‖ ^ 2 < quadForm P φ) →
        (k : Cardinal) ≤ Module.rank ℂ (LinearMap.range (P (Set.Ioi lam) : H →ₗ[ℂ] H))) := by sorry

end TeschlQM.MinMax
