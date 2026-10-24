-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_conditional_two_product_zero
-- name    : QAlgorithms.Papers.Independent.Information100.P60.conditional_two_product_zero
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:42:32.310996+00:00
-- url     : https://prove2.me/theorems/826eaf21-f027-437f-b08b-9bdcbda75a78
-- title:
--   Corollary 4.1: conditional MU-convertible consequence of Conjecture 1
-- statement:
--   Let $\mathrm{MU}_d$ be the finite convex mixtures of unitary conjugations on $\mathbb C^d$. Write $E_{r,k}^c(\mathcal N)$ for the operational parallel block-i.i.d. Stein exponent against this composite i.i.d. null class, in bits, with a uniform Type-I constraint, local reference dimension $r$, and the zero-error outer limit taken after the block-count liminf and limsup. The value $r=1$ means no memory and $r=d$ supplies sufficient memory. Assume the full Conjecture-1 predicate: for every pair of qutrit density operators $\rho_1,\rho_2$, there exist $U,V\in U(3)$ such that $\tfrac12(U\rho_iU^\dagger+V\rho_iV^\dagger)=\mathcal N_{WH}(\rho_i)$ for $i=1,2$, where $\mathcal N_{WH}(X)=(\operatorname{Tr}(X)I-X^T)/2$. Let $\overline{\mathcal N}$ be CPTP and outside $\mathrm{MU}_3$, and suppose some $O(3)$-covariant CPTP $\mathcal N$ is MU-convertible to it. Then $$E_{1,2}^{\mathrm{product}}(\overline{\mathcal N})=0.$$ This corollary is conditional; the conjecture is not asserted as a proved result.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 24, Corollary 4.1: conditional MU-convertible consequence of Conjecture 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF p.24, Corollary 4.1, explicitly conditional on Conjecture 1. -/
theorem conditional_two_product_zero (hconj : TwoProbeConjecture) (M : Maps 3 3)
    (hM : IsChannel M) (hn : M ∉ MU 3)
    (hc : ∃ N : Maps 3 3, IsChannel N ∧ OrthogonalCovariant N ∧ MUConvertible N M) :
    blockExponent 1 (MU 3) M 2 .product = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
