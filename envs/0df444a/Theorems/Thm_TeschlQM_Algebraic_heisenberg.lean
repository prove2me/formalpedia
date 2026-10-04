-- Prove2me | Theorems.Thm_TeschlQM_Algebraic_heisenberg
-- name    : TeschlQM.Algebraic.heisenberg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T03:10:11.878176+00:00
-- url     : https://prove2.me/theorems/08e81200-d3ab-4f8d-b766-f6c822a8ab40
-- title:
--   Theorem 8.2 — Heisenberg uncertainty principle Δ_ψ(A)Δ_ψ(B) ≥ ½|𝔼_ψ([A,B])|
-- statement:
--   Let $A$ and $B$ be symmetric operators in a complex Hilbert space $\mathfrak H$, and let $\psi$ be a state ($\|\psi\| = 1$) with $\psi \in \mathfrak D(AB) \cap \mathfrak D(BA)$, i.e. $\psi \in \mathfrak D(A) \cap \mathfrak D(B)$, $B\psi \in \mathfrak D(A)$ and $A\psi \in \mathfrak D(B)$. With $[A, B]\psi = AB\psi - BA\psi$,
--   $$\Delta_\psi(A)\,\Delta_\psi(B) \ge \frac12 \big|\mathbb E_\psi([A, B])\big| = \frac12\big|\langle \psi, AB\psi - BA\psi\rangle\big|.$$
--   Equality holds if $(B - \mathbb E_\psi(B))\psi = i\lambda (A - \mathbb E_\psi(A))\psi$ for some $\lambda \in \mathbb R \setminus \{0\}$, or if $\psi$ is an eigenvector of $A$ or of $B$.
--
--   For position and momentum this gives $\Delta_\psi(p_j)\Delta_\psi(x_k) \ge \delta_{jk}/2$.
--
--   **Formalization Note.** $\mathbb E_\psi(A) = \langle\psi, A\psi\rangle$ and $\Delta_\psi(A) = \|A\psi - \mathbb E_\psi(A)\psi\|$ are Teschl's (2.5)–(2.6), which presuppose a state; the hypothesis $\|\psi\| = 1$ is added explicitly (without it the inequality fails by scaling). The equality clause is an implication, as in the book, not an equivalence.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 174, Theorem 8.2

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Algebraic_expectation

namespace TeschlQM.Algebraic

open scoped InnerProductSpace

/-- Teschl, Theorem 8.2 (Heisenberg Uncertainty Principle), p. 174. For symmetric `A`, `B` and a
state `ψ ∈ 𝔇(AB) ∩ 𝔇(BA)` (`‖ψ‖ = 1`),
`Δ_ψ(A) Δ_ψ(B) ≥ ½ |𝔼_ψ([A, B])|` with `[A, B]ψ = ABψ − BAψ` (8.10), and equality holds if
`(B − 𝔼_ψ(B))ψ = iλ(A − 𝔼_ψ(A))ψ` for some real `λ ≠ 0` (8.11), or if `ψ` is an eigenstate of `A`
or of `B`. -/
theorem heisenberg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (hB : TeschlQM.Shared.IsSymmetric B)
    (ψ : H) (hψ : ‖ψ‖ = 1) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain)
    (hAB : B ⟨ψ, hψB⟩ ∈ A.domain) (hBA : A ⟨ψ, hψA⟩ ∈ B.domain) :
    deviation A ⟨ψ, hψA⟩ * deviation B ⟨ψ, hψB⟩ ≥
        1 / 2 * ‖⟪ψ, A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ⟨ψ, hψA⟩, hBA⟩⟫_ℂ‖ ∧
      ((∃ lam : ℝ, lam ≠ 0 ∧
          B ⟨ψ, hψB⟩ - expectation B ⟨ψ, hψB⟩ • ψ =
            (Complex.I * lam) • (A ⟨ψ, hψA⟩ - expectation A ⟨ψ, hψA⟩ • ψ)) ∨
        (∃ a : ℂ, A ⟨ψ, hψA⟩ = a • ψ) ∨ (∃ b : ℂ, B ⟨ψ, hψB⟩ = b • ψ) →
        deviation A ⟨ψ, hψA⟩ * deviation B ⟨ψ, hψB⟩ =
          1 / 2 * ‖⟪ψ, A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ⟨ψ, hψA⟩, hBA⟩⟫_ℂ‖) := by sorry

end TeschlQM.Algebraic
