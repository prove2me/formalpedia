-- Prove2me | Theorems.Thm_UnphysicalHilbert_prop7_equal_mixtures_same_span
-- name    : UnphysicalHilbert.prop7_equal_mixtures_same_span
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:04:02.473973+00:00
-- url     : https://prove2.me/theorems/2aed40f8-c3cf-4785-a71b-47ccbaf8fb79
-- title:
--   Proposition 7 — equal mixtures have equal spans
-- statement:
--   Let $H$ be a complex inner product space and let $(\psi_i)_{i\in I}$, $(\phi_j)_{j\in J}$ be finite families of unit vectors. Suppose there are weights $a_i>0$, $b_j>0$ with $\sum_i a_i=1$, $\sum_j b_j=1$ and
--   $$\sum_{i\in I} a_i\,|\psi_i\rangle\langle\psi_i|=\sum_{j\in J} b_j\,|\phi_j\rangle\langle\phi_j| .$$
--   Then
--   $$\operatorname{span}\{\psi_i : i\in I\}=\operatorname{span}\{\phi_j : j\in J\}.$$
--
--   Two decompositions of the same mixed state into pure states involve pure states from the same subspace; this is one direction of the paper's identification of superposition with non-unique decomposition of mixtures (Proposition 9).
--
--   **Formalization Note** Finite sets are encoded as finite indexed families; $H$ need not be complete.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Appendix A, p. 8, Proposition 7

import Definitions.Def_UnphysicalHilbert_StateSpace

namespace UnphysicalHilbert

/-- Proposition 7: two finite families of pure states giving the same strictly convex
mixture span the same subspace. -/
theorem prop7_equal_mixtures_same_span
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ψ : ι → H) (ϕ : κ → H) (hψ : IsNormalizedFamily ψ) (hϕ : IsNormalizedFamily ϕ)
    (a : ι → ℝ) (b : κ → ℝ) (ha : IsStrictConvexWeights a) (hb : IsStrictConvexWeights b)
    (hab : mixture a ψ = mixture b ϕ) :
    Submodule.span ℂ (Set.range ψ) = Submodule.span ℂ (Set.range ϕ) := by
  sorry

end UnphysicalHilbert
