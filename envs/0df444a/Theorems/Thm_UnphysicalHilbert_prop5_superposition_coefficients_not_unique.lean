-- Prove2me | Theorems.Thm_UnphysicalHilbert_prop5_superposition_coefficients_not_unique
-- name    : UnphysicalHilbert.prop5_superposition_coefficients_not_unique
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T21:03:35.852911+00:00
-- url     : https://prove2.me/theorems/a263f752-e039-486a-a5a9-91fc4ab9237f
-- title:
--   Proposition 5 — rays do not determine superposition coefficients
-- statement:
--   Let $H$ be a complex vector space and $\mathbb P(H)$ its projective space; write $[v]\in\mathbb P(H)$ for the ray of a nonzero vector $v$. Let $\phi_1,\phi_2\in H$ be nonzero and suppose
--   $$\psi=c_1\phi_1+c_2\phi_2,\qquad c_1,c_2\in\mathbb C\setminus\{0\}.$$
--   Then for every pair $\hat c_1,\hat c_2\in\mathbb C\setminus\{0\}$ there are nonzero $\hat\phi_1,\hat\phi_2\in H$ with
--   $$[\hat\phi_1]=[\phi_1],\qquad[\hat\phi_2]=[\phi_2],\qquad \psi=\hat c_1\hat\phi_1+\hat c_2\hat\phi_2 .$$
--
--   Without an inner product, the coefficients of a linear combination of states are therefore not determined by the rays involved.
--
--   **Formalization Note** The paper allows arbitrary coefficients; nonvanishing of $c_i$ and $\hat c_i$ is added because the statement is false otherwise (e.g. $\hat c_1=0$ with $\phi_1,\phi_2$ independent), and the paper's proof divides by these coefficients.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Appendix A, pp. 7–8, Proposition 5 and eq. (6)

import Mathlib

namespace UnphysicalHilbert

/-- Proposition 5: rays alone do not fix the coefficients of a linear combination. -/
theorem prop5_superposition_coefficients_not_unique
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (ψ ϕ₁ ϕ₂ : H) (hϕ₁ : ϕ₁ ≠ 0) (hϕ₂ : ϕ₂ ≠ 0) (c₁ c₂ : ℂ) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hψ : ψ = c₁ • ϕ₁ + c₂ • ϕ₂) (d₁ d₂ : ℂ) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    ∃ (χ₁ χ₂ : H) (hχ₁ : χ₁ ≠ 0) (hχ₂ : χ₂ ≠ 0),
      Projectivization.mk ℂ χ₁ hχ₁ = Projectivization.mk ℂ ϕ₁ hϕ₁ ∧
      Projectivization.mk ℂ χ₂ hχ₂ = Projectivization.mk ℂ ϕ₂ hϕ₂ ∧
      ψ = d₁ • χ₁ + d₂ • χ₂ := by
  sorry

end UnphysicalHilbert
