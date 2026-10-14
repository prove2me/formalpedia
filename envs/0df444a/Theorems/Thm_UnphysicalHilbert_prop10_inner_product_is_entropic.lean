-- Prove2me | Theorems.Thm_UnphysicalHilbert_prop10_inner_product_is_entropic
-- name    : UnphysicalHilbert.prop10_inner_product_is_entropic
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T21:06:35.573151+00:00
-- url     : https://prove2.me/theorems/5fedc74c-7263-4540-8e49-0e80cd3140a4
-- title:
--   Proposition 10 — the inner product is an entropic structure
-- statement:
--   Let $H$ be a complex inner product space and, for unit vectors $\psi,\phi\in H$, let $I(\psi,\phi)$ be the von Neumann entropy of the equal mixture $\tfrac12|\psi\rangle\langle\psi|+\tfrac12|\phi\rangle\langle\phi|$. Define
--   $$f(p)=-\frac{1+p}{2}\log\frac{1+p}{2}-\frac{1-p}{2}\log\frac{1-p}{2}\qquad(0\log0=0).$$
--   Then:
--
--   1. for all unit vectors $\psi,\phi\in H$,
--   $$I(\psi,\phi)=f\bigl(|\langle\psi,\phi\rangle|\bigr);$$
--   2. $f$ is injective on $[0,1]$.
--
--   Hence the transition probability $|\langle\psi,\phi\rangle|^2$ and the entropy of the equal mixture determine each other.
--
--   **Formalization Note** The entropy is computed on $\operatorname{span}\{\psi,\phi\}$ (see the definition file). The paper's eq. (13) is stated for $p=|\langle\psi|\phi\rangle|^2$, while its explicit formula (17)–(18) uses $|\langle\psi|\phi\rangle|$; since $t\mapsto t^2$ is a bijection of $[0,1]$, the formal version (explicit formula plus injectivity) implies both readings.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Appendix A, pp. 9–10, Proposition 10, eqs. (11)–(18)

import Definitions.Def_UnphysicalHilbert_StateSpace

namespace UnphysicalHilbert

open scoped InnerProductSpace

/-- Proposition 10: the entropy of the equal mixture of two pure states is an invertible
function of the modulus of their inner product. -/
theorem prop10_inner_product_is_entropic
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (∀ ψ ϕ : H, ‖ψ‖ = 1 → ‖ϕ‖ = 1 →
      equalMixtureEntropy ψ ϕ =
        Real.negMulLog ((1 + ‖⟪ψ, ϕ⟫_ℂ‖) / 2) + Real.negMulLog ((1 - ‖⟪ψ, ϕ⟫_ℂ‖) / 2)) ∧
    Set.InjOn (fun p : ℝ => Real.negMulLog ((1 + p) / 2) + Real.negMulLog ((1 - p) / 2))
      (Set.Icc 0 1) := by
  sorry

end UnphysicalHilbert
