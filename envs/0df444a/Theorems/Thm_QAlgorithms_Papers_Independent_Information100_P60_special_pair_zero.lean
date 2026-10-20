-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_special_pair_zero
-- name    : QAlgorithms.Papers.Independent.Information100.P60.special_pair_zero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:41:23.302254+00:00
-- url     : https://prove2.me/theorems/975677e7-cbb2-4df9-a691-04e355d78f81
-- title:
--   Proposition 1: special pairs of qutrit product probes have zero fixed-probe exponent
-- statement:
--   Let $\mathrm{MU}_d$ be the finite convex mixtures of unitary conjugations on $\mathbb C^d$. Write $E_{r,k}^c(\mathcal N)$ for the operational parallel block-i.i.d. Stein exponent against this composite i.i.d. null class, in bits, with a uniform Type-I constraint, local reference dimension $r$, and the zero-error outer limit taken after the block-count liminf and limsup. The value $r=1$ means no memory and $r=d$ supplies sufficient memory. Let $\mathcal N$ be an $O(3)$-covariant CPTP channel outside $\mathrm{MU}_3$, and let $\rho_1,\rho_2$ be qutrit density operators. Suppose that both are real in the transpose basis, or they commute, or they have a common nonzero eigenvector, or either has an eigenspace of dimension at least two, or either is pure. Then the specified block probe has $$E_{\mathrm{fixed}}(\rho_1\otimes\rho_2;\mathcal N)=0.$$ The fixed exponent repeats this probe independently and optimizes only the test. This includes every listed sufficient case and does not assert vanishing for the optimization over all pairs. Both outer limiting values exist and equal zero.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 24, Proposition 1: special pairs of qutrit product probes have zero fixed-probe exponent

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF pp.20,23–24, Proposition 1: fixed specified pair, not an optimized exponent. -/
theorem special_pair_zero (N : Maps 3 3) (hN : IsChannel N) (hn : N ∉ MU 3)
    (hc : OrthogonalCovariant N) (rho sigma : Mat (Fin 3))
    (hr : IsDensityMatrix rho) (hs : IsDensityMatrix sigma) (h : SpecialPair rho sigma) :
    HasSteinValue (blockRate 1 (MU 3) N 2 {plainProduct ![rho, sigma]}) 0 ∧
    fixedExponent 1 (MU 3) N 2 (plainProduct ![rho, sigma]) = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
