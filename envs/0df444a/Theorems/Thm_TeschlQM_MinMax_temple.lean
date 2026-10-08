-- Prove2me | Theorems.Thm_TeschlQM_MinMax_temple
-- name    : TeschlQM.MinMax.temple
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:49:16.272747+00:00
-- url     : https://prove2.me/theorems/1327ebf8-2c58-4b38-a3e4-3767fe53bcf6
-- title:
--   Theorem 4.13 — Temple's inequality
-- statement:
--   Let $A$ be a self-adjoint operator on a complex Hilbert space $\mathfrak H$, let $\lambda_1 < \lambda_2$, and let $\psi \in \mathfrak D(A)$ with $\|\psi\| = 1$ such that
--   $$\lambda = \langle \psi, A\psi \rangle \in (\lambda_1, \lambda_2).$$
--   If there is exactly one point $E$ of the spectrum between $\lambda_1$ and $\lambda_2$, that is $\sigma(A) \cap (\lambda_1, \lambda_2) = \{E\}$ (then $E$ is an isolated eigenvalue), then
--   $$\lambda - \frac{\|(A - \lambda)\psi\|^2}{\lambda_2 - \lambda} \le E \le \lambda + \frac{\|(A - \lambda)\psi\|^2}{\lambda - \lambda_1}.$$
--
--   Together with the variational upper bound, Temple's inequality gives a computable two-sided enclosure of an isolated eigenvalue from a single trial vector and its residual.
--
--   **Formalization Note.** $\sigma(A)$ is the resolvent spectrum of p. 73, and $\sigma(A) \cap (\lambda_1, \lambda_2)$ is the set of real $x \in (\lambda_1, \lambda_2)$ with $x \in \sigma(A)$. That $E$ is an eigenvalue is not assumed; it follows from the hypotheses. The hypothesis $\lambda = \langle\psi, A\psi\rangle$ is an equality of complex numbers.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 120, Theorem 4.13

import Mathlib
import Definitions.Def_TeschlQM_MinMax_spectrum

open scoped InnerProductSpace

namespace TeschlQM.MinMax

/-- Teschl, Theorem 4.13 (Temple's inequality), p. 120, (4.37)–(4.38): let `A` be self-adjoint,
`λ₁ < λ₂` and `ψ ∈ 𝔇(A)` with `‖ψ‖ = 1` such that `λ = ⟨ψ, Aψ⟩ ∈ (λ₁, λ₂)`. If
`σ(A) ∩ (λ₁, λ₂) = {E}` (one isolated eigenvalue `E` between `λ₁` and `λ₂`), then
`λ − ‖(A − λ)ψ‖²/(λ₂ − λ) ≤ E ≤ λ + ‖(A − λ)ψ‖²/(λ − λ₁)`. -/
theorem temple {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (lam₁ lam₂ : ℝ) (hlt : lam₁ < lam₂)
    (ψ : A.domain) (hψ : ‖(ψ : H)‖ = 1) (lam : ℝ) (hlam : ⟪(ψ : H), A ψ⟫_ℂ = (lam : ℂ))
    (hmem : lam ∈ Set.Ioo lam₁ lam₂) (E : ℝ)
    (hE : {x : ℝ | (x : ℂ) ∈ spectrum A} ∩ Set.Ioo lam₁ lam₂ = {E}) :
    lam - ‖A ψ - (lam : ℂ) • (ψ : H)‖ ^ 2 / (lam₂ - lam) ≤ E ∧
      E ≤ lam + ‖A ψ - (lam : ℂ) • (ψ : H)‖ ^ 2 / (lam - lam₁) := by sorry

end TeschlQM.MinMax
