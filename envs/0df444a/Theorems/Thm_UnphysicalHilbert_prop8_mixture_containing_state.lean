-- Prove2me | Theorems.Thm_UnphysicalHilbert_prop8_mixture_containing_state
-- name    : UnphysicalHilbert.prop8_mixture_containing_state
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:04:53.409803+00:00
-- url     : https://prove2.me/theorems/42fe4f2d-8811-4e22-a5e8-df48f9686cdc
-- title:
--   Proposition 8 (corrected) — a mixture can be decomposed to include a given state
-- statement:
--   Let $H$ be a complex inner product space, $\psi\in H$ a unit vector, and $\rho:H\to H$ a finite-rank density operator, i.e. $\rho=\sum_{k} b_k|\phi_k\rangle\langle\phi_k|$ for finitely many unit vectors $\phi_k$ and weights $b_k>0$ with $\sum_k b_k=1$. Assume
--   $$\psi\in\operatorname{range}(\rho).$$
--   Then there are $n\ge0$, unit vectors $\psi_0,\psi_1,\dots,\psi_n$ with $\psi_0=\psi$, and weights $p_0,\dots,p_n>0$ with $\sum_k p_k=1$, such that
--   $$\rho=\sum_{k=0}^{n}p_k\,|\psi_k\rangle\langle\psi_k| .$$
--
--   Any finite-rank mixed state whose support contains $\psi$ can be prepared as a mixture in which the pure state $\psi$ occurs with positive weight.
--
--   **Formalization Note** The paper's hypothesis is $\langle\psi|\rho|\psi\rangle\neq0$. That hypothesis is insufficient: for $\rho=|e_0\rangle\langle e_0|$ and $\psi=(e_0+e_1)/\sqrt2$ in $\mathbb C^2$, $\langle\psi|\rho|\psi\rangle=\tfrac12$ but no such decomposition exists. The hypothesis is therefore replaced by $\psi\in\operatorname{range}(\rho)$, which is exactly what the paper's proof of Proposition 9 supplies. The first vector is indexed by $0$.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Appendix A, pp. 8–9, Proposition 8 (hypothesis corrected, see note)

import Definitions.Def_UnphysicalHilbert_StateSpace

namespace UnphysicalHilbert

/-- Proposition 8 (corrected): a finite-rank density operator `ρ` whose range contains the
normalized vector `ψ` is a strictly convex combination of finitely many pure states, the
first of which is `|ψ⟩⟨ψ|`. (The paper's hypothesis `⟨ψ|ρ|ψ⟩ ≠ 0` is replaced by
`ψ ∈ range ρ`; with the original hypothesis the statement fails, e.g. for
`ρ = |e₀⟩⟨e₀|`, `ψ = (e₀ + e₁)/√2` in `ℂ²`.) -/
theorem prop8_mixture_containing_state
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : H) (hψ : ‖ψ‖ = 1) (ρ : H →ₗ[ℂ] H) (hρ : IsFiniteRankDensityOperator ρ)
    (hψρ : ψ ∈ LinearMap.range ρ) :
    ∃ (n : ℕ) (p : Fin (n + 1) → ℝ) (φ : Fin (n + 1) → H),
      φ 0 = ψ ∧ IsNormalizedFamily φ ∧ IsStrictConvexWeights p ∧ ρ = mixture p φ := by
  sorry

end UnphysicalHilbert
