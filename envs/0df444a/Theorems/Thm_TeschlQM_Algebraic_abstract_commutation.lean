-- Prove2me | Theorems.Thm_TeschlQM_Algebraic_abstract_commutation
-- name    : TeschlQM.Algebraic.abstract_commutation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T03:20:04.242596+00:00
-- url     : https://prove2.me/theorems/f57ffa6e-b5f2-4727-b84c-c5eab0a0a785
-- title:
--   Theorem 8.6 — A*A on Ker(A)^⊥ and AA* on Ker(A*)^⊥ are unitarily equivalent; eigenvectors and resolvents
-- statement:
--   Let $A$ be a closed, densely defined operator in a complex Hilbert space $\mathfrak H$, and let $H_0 = A^*A$ and $H_1 = AA^*$ with their natural domains $\mathfrak D(A^*A) = \{\psi \in \mathfrak D(A) \mid A\psi \in \mathfrak D(A^*)\}$ and similarly for $AA^*$. Then:
--   1. The parts $H_0|_{\operatorname{Ker}(A)^\perp}$ and $H_1|_{\operatorname{Ker}(A^*)^\perp}$ are unitarily equivalent: there is a unitary $U : \operatorname{Ker}(A)^\perp \to \operatorname{Ker}(A^*)^\perp$ such that for all $\psi, \varphi \in \operatorname{Ker}(A)^\perp$,
--   $$\psi \in \mathfrak D(H_0),\ H_0\psi = \varphi \iff U\psi \in \mathfrak D(H_1),\ H_1 U\psi = U\varphi.$$
--   2. If $H_0\psi_0 = E\psi_0$ with $\psi_0 \in \mathfrak D(H_0) \cap \operatorname{Ker}(A)^\perp$ and $E \in \mathbb R$, then $\psi_1 = A\psi_0 \in \mathfrak D(H_1) \cap \operatorname{Ker}(A^*)^\perp$, $H_1\psi_1 = E\psi_1$ and $\|\psi_1\| = \sqrt E\,\|\psi_0\|$.
--   3. For $z \ne 0$ in $\rho(H_0) \cap \rho(H_1)$,
--   $$R_{H_1}(z) \supseteq \frac1z\big(A R_{H_0}(z) A^* - 1\big), \qquad R_{H_0}(z) \supseteq \frac1z\big(A^* R_{H_1}(z) A - 1\big),$$
--   i.e. $R_{H_1}(z)\varphi = z^{-1}(A R_{H_0}(z) A^*\varphi - \varphi)$ whenever $\varphi \in \mathfrak D(A^*)$ and $R_{H_0}(z)A^*\varphi \in \mathfrak D(A)$, and symmetrically.
--
--   This "supersymmetric" pairing transports eigenvalues and eigenvectors between $A^*A$ and $AA^*$; the book uses it for the hydrogen atom.
--
--   **Formalization Note.** $A^*$ is Mathlib's `LinearPMap.adjoint`, meaningful because the domain of $A$ is assumed dense (Teschl's standing convention for operators having an adjoint). $H_0$, $H_1$ are `opComp A.adjoint A` and `opComp A A.adjoint`; unitary equivalence of the parts is stated as graph correspondence under a `LinearIsometryEquiv` between the orthogonal complements. Resolvents are bounded operators `R` with `IsResolventAt`. **Correction:** the book prints "$H_1\psi_1 = \psi_1$"; the proof and the norm identity require $H_1\psi_1 = E\psi_1$, which is what is stated. In (8.48), $H_0, H_1$ are the operators on all of $\mathfrak H$, as in the book's proof ($P_1 = P_{H_1}(\{0\})$).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 180, Theorem 8.6

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Algebraic_opComp

namespace TeschlQM.Algebraic

/-- Teschl, Theorem 8.6, p. 180. Let `A` be a closed, densely defined operator, `H₀ = A*A` and
`H₁ = AA*` (with their natural domains).
1. The parts `H₀|_{Ker(A)^⊥}` and `H₁|_{Ker(A*)^⊥}` are unitarily equivalent: there is a unitary
   `U : Ker(A)^⊥ → Ker(A*)^⊥` mapping the graph of the first onto the graph of the second.
2. If `H₀ψ₀ = Eψ₀`, `ψ₀ ∈ 𝔇(H₀) ∩ Ker(A)^⊥`, then `ψ₁ = Aψ₀ ∈ 𝔇(H₁) ∩ Ker(A*)^⊥`,
   `H₁ψ₁ = Eψ₁` (the book prints `H₁ψ₁ = ψ₁`, a misprint) and `‖ψ₁‖ = √E ‖ψ₀‖`.
3. (8.48): for `z ≠ 0` in `ρ(H₀) ∩ ρ(H₁)`,
   `R_{H₁}(z) ⊇ (1/z)(A R_{H₀}(z) A* − 1)` and `R_{H₀}(z) ⊇ (1/z)(A* R_{H₁}(z) A − 1)`. -/
theorem abstract_commutation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : A.IsClosed) (hdense : Dense (A.domain : Set H)) :
    (∃ U : (opKer A)ᗮ ≃ₗᵢ[ℂ] (opKer A.adjoint)ᗮ, ∀ ψ φ : (opKer A)ᗮ,
      (∃ h : (ψ : H) ∈ (opComp A.adjoint A).domain, opComp A.adjoint A ⟨ψ, h⟩ = φ) ↔
        (∃ h : ((U ψ : (opKer A.adjoint)ᗮ) : H) ∈ (opComp A A.adjoint).domain,
          opComp A A.adjoint ⟨U ψ, h⟩ = U φ)) ∧
    (∀ (E : ℝ) (ψ₀ : H) (h₀ : ψ₀ ∈ (opComp A.adjoint A).domain), ψ₀ ∈ (opKer A)ᗮ →
      opComp A.adjoint A ⟨ψ₀, h₀⟩ = (E : ℂ) • ψ₀ →
        ∃ h₁ : ψ₀ ∈ A.domain, ∃ h₂ : A ⟨ψ₀, h₁⟩ ∈ (opComp A A.adjoint).domain,
          A ⟨ψ₀, h₁⟩ ∈ (opKer A.adjoint)ᗮ ∧
            opComp A A.adjoint ⟨A ⟨ψ₀, h₁⟩, h₂⟩ = (E : ℂ) • A ⟨ψ₀, h₁⟩ ∧
              ‖A ⟨ψ₀, h₁⟩‖ = Real.sqrt E * ‖ψ₀‖) ∧
    (∀ z : ℂ, z ≠ 0 → ∀ R₀ R₁ : H →L[ℂ] H,
      TeschlQM.Shared.IsResolventAt (opComp A.adjoint A) z R₀ → TeschlQM.Shared.IsResolventAt (opComp A A.adjoint) z R₁ →
        (∀ (φ : H) (h : φ ∈ A.adjoint.domain) (h' : R₀ (A.adjoint ⟨φ, h⟩) ∈ A.domain),
          R₁ φ = z⁻¹ • (A ⟨R₀ (A.adjoint ⟨φ, h⟩), h'⟩ - φ)) ∧
        (∀ (φ : H) (h : φ ∈ A.domain) (h' : R₁ (A ⟨φ, h⟩) ∈ A.adjoint.domain),
          R₀ φ = z⁻¹ • (A.adjoint ⟨R₁ (A ⟨φ, h⟩), h'⟩ - φ))) := by sorry

end TeschlQM.Algebraic
