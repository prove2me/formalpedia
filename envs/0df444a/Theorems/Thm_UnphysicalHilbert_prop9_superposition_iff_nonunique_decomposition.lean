-- Prove2me | Theorems.Thm_UnphysicalHilbert_prop9_superposition_iff_nonunique_decomposition
-- name    : UnphysicalHilbert.prop9_superposition_iff_nonunique_decomposition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:05:48.088055+00:00
-- url     : https://prove2.me/theorems/a9315adb-0530-49a4-8465-1534e3f1132a
-- title:
--   Proposition 9 — superposition is non-unique decomposition of mixed states
-- statement:
--   Let $H$ be a complex inner product space, $\psi\in H$ a unit vector, and $(\phi_j)_{j\in J}$ a finite family of unit vectors with $\phi_j\neq\psi$ for all $j$. Then the following are equivalent:
--
--   1. $\psi\in\operatorname{span}\{\phi_j : j\in J\}$;
--   2. there exist $n\ge0$, unit vectors $\psi_0=\psi,\psi_1,\dots,\psi_n$, and weights $a_0,\dots,a_n>0$, $b_j>0$ with $\sum_k a_k=1$, $\sum_j b_j=1$ and
--   $$\sum_{k=0}^{n}a_k\,|\psi_k\rangle\langle\psi_k|=\sum_{j\in J}b_j\,|\phi_j\rangle\langle\phi_j| .$$
--
--   A pure state is a superposition of given pure states exactly when some mixture of those states can also be prepared as a mixture that includes the given state.
--
--   **Formalization Note** The paper says "complex vector space", but normalization and the operators $|\psi\rangle\langle\psi|$ require an inner product, so $H$ is a complex inner product space (not necessarily complete). The distinguished vector is indexed by $0$.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Appendix A, p. 9, Proposition 9

import Definitions.Def_UnphysicalHilbert_StateSpace

namespace UnphysicalHilbert

/-- Proposition 9: superposition is non-unique decomposition of mixed states. -/
theorem prop9_superposition_iff_nonunique_decomposition
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι]
    (ψ : H) (hψ : ‖ψ‖ = 1) (ϕ : ι → H) (hϕ : IsNormalizedFamily ϕ) (hψϕ : ∀ j, ϕ j ≠ ψ) :
    ψ ∈ Submodule.span ℂ (Set.range ϕ) ↔
      ∃ (n : ℕ) (φ : Fin (n + 1) → H) (a : Fin (n + 1) → ℝ) (b : ι → ℝ),
        φ 0 = ψ ∧ IsNormalizedFamily φ ∧ IsStrictConvexWeights a ∧
        IsStrictConvexWeights b ∧ mixture a φ = mixture b ϕ := by
  sorry

end UnphysicalHilbert
