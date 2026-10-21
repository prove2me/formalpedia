-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_invariantCharacterExpansion
-- name    : QAlgorithms.Papers.Independent.Next46.P36.invariantCharacterExpansion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:46:30.581027+00:00
-- url     : https://prove2.me/theorems/dfb225ff-7e7f-4587-ad05-20e33fc7f76e
-- title:
--   Proposition 2: invariant costs have an L2 character expansion
-- statement:
--   Let $G$ be compact with normalized two-sided Haar measure and let $\{U^\mu\}$ be a complete collection of pairwise inequivalent based continuous unitary irreducible representations. Let the measurable complex-valued function $c(\hat g,g)$ be left- and right-invariant, with $c(\cdot,1)\in L^2(G)$. Define $\chi_\mu=\operatorname{Tr}U^\mu$ and
--
--   $$a_\mu=\int_Gc(h,1)\overline{\chi_\mu(h)}\,dh.$$
--
--   For every $g$, finite character partial sums converge to $c(\cdot,g)$ in squared $L^2$ error:
--
--   $$\lim_{F\uparrow\widehat G}\int_G\left|c(h,g)-\sum_{\mu\in F}a_\mu\chi_\mu(g^{-1}h)\right|^2dh=0.$$
--
--   Here $F$ ranges over finite subsets of the unitary dual. If $G$ is finite, only finitely many coefficients are nonzero and the character series equals $c(h,g)$ at every pair. There is no coefficient sign restriction. This follows the proof's $L^2$ interpretation, rather than asserting pointwise convergence for arbitrary functions.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 10, Appendix Proposition 2, Eq. (70)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF p.10 Proposition 2 Eq.(70): the proof's L2 interpretation of the
character expansion, with its UNconjugated-character convention. The finite-group
case also has a finite-support, pointwise expansion. No Fourier sign assumption. -/
theorem invariantCharacterExpansion
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (dg : Measure G) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (K : IrrepCatalog G) (cost : G → G → ℂ) (hi : InvariantCost cost)
    (hm : Measurable (Function.uncurry cost))
    (hL2 : MemLp (fun g => cost g 1) 2 dg) :
    ∃ a : K.Label → ℂ,
      (∀ s, a s = ∫ g, cost g 1 * conj (((K.rep s).matrix g).trace) ∂dg) ∧
      (∀ g, Tendsto (fun F : Finset K.Label =>
        ∫ h, ‖cost h g - ∑ s ∈ F, a s * ((K.rep s).matrix (g⁻¹ * h)).trace‖ ^ 2 ∂dg)
        atTop (nhds 0)) ∧
      (Finite G → (Function.support a).Finite ∧
        ∀ h g, HasSum (fun s => a s * ((K.rep s).matrix (g⁻¹ * h)).trace) (cost h g)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
