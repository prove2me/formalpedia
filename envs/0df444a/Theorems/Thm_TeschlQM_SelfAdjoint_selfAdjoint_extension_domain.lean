-- Prove2me | Theorems.Thm_TeschlQM_SelfAdjoint_selfAdjoint_extension_domain
-- name    : TeschlQM.SelfAdjoint.selfAdjoint_extension_domain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:24:15.188913+00:00
-- url     : https://prove2.me/theorems/63bd84ce-810c-4886-b18e-5778067ae028
-- title:
--   Theorem 2.26, (2.103)–(2.104) — domain and action of a self-adjoint extension
-- statement:
--   Let $A$ be a closed symmetric operator on a complex Hilbert space, let $A_1$ be a self-adjoint extension of $A$ and let $V_1$ be the Cayley transform of $A_1$. With $K_+ = \operatorname{Ran}(A + \mathrm{i})^\perp$,
--   $$\mathfrak{D}(A_1) = \mathfrak{D}(A) + (1 - V_1)K_+ = \{\psi + \varphi_+ - V_1\varphi_+ \mid \psi \in \mathfrak{D}(A),\ \varphi_+ \in K_+\}$$
--   and
--   $$A_1(\psi + \varphi_+ - V_1\varphi_+) = A\psi + \mathrm{i}\varphi_+ + \mathrm{i}V_1\varphi_+.$$
--
--   **Formalization Note.** The hypothesis that $A$ is closed is added. The book states (2.103) for every symmetric $A$, but for a non-closed one it fails: if $A$ is essentially self-adjoint and not closed, then $K_+ = \{0\}$ and $\mathfrak{D}(A_1) = \mathfrak{D}(\overline{A}) \ne \mathfrak{D}(A)$. The book's proof uses $\mathfrak{H} = \operatorname{Ran}(A+\mathrm{i}) \oplus K_+$, which holds exactly when $\operatorname{Ran}(A + \mathrm{i})$ is closed (Lemma 2.27). Since $A_1$ is self-adjoint, $\mathfrak{D}(V_1) = \mathfrak{H}$, so letting $\varphi_+$ range over $\mathfrak{D}(V_1) \cap K_+$ is the same as letting it range over $K_+$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 82, Theorem 2.26, Eqs. (2.103)–(2.104)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_IsCayleyTransform
import Definitions.Def_TeschlQM_SelfAdjoint_defectSpace

namespace TeschlQM.SelfAdjoint

/-- Teschl, Theorem 2.26, (2.103)–(2.104) (p. 82): let `A₁` be a self-adjoint extension of the
symmetric operator `A` and `V₁` its Cayley transform. Then
`𝔇(A₁) = {ψ + φ₊ - V₁φ₊ | ψ ∈ 𝔇(A), φ₊ ∈ K₊}` and `A₁(ψ + φ₊ - V₁φ₊) = Aψ + iφ₊ + iV₁φ₊`.
The hypothesis that `A` is closed is added: without it (2.103) fails (for an essentially
self-adjoint, non-closed `A`, `K₊ = {0}` and `𝔇(A₁) = 𝔇(Ā) ≠ 𝔇(A)`). `𝔇(V₁) = ℌ` since `A₁` is
self-adjoint, so quantifying `φ₊` over `𝔇(V₁) ∩ K₊` is quantifying over `K₊`. -/
theorem selfAdjoint_extension_domain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A A₁ V₁ : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (hAc : A.IsClosed)
    (hA₁ : IsSelfAdjoint A₁) (hAA₁ : A ≤ A₁) (hV₁ : IsCayleyTransform A₁ V₁) :
    (A₁.domain : Set H) =
        {x : H | ∃ ψ : A.domain, ∃ φ : V₁.domain, (φ : H) ∈ defectPlus A ∧
          x = (ψ : H) + (φ : H) - V₁ φ} ∧
      ∀ (ψ : A.domain) (φ : V₁.domain), (φ : H) ∈ defectPlus A →
        ∀ h : (ψ : H) + (φ : H) - V₁ φ ∈ A₁.domain,
          A₁ ⟨(ψ : H) + (φ : H) - V₁ φ, h⟩ = A ψ + Complex.I • (φ : H) + Complex.I • V₁ φ := by sorry

end TeschlQM.SelfAdjoint
