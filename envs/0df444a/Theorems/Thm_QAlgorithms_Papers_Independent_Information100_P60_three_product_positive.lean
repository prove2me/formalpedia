-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_three_product_positive
-- name    : QAlgorithms.Papers.Independent.Information100.P60.three_product_positive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:43:10.660326+00:00
-- url     : https://prove2.me/theorems/988c0d15-4f29-458d-a17a-006a51489128
-- title:
--   Theorem 5: three product probes suffice for the qutrit Werner-Holevo channel
-- statement:
--   Let $\mathrm{MU}_d$ be the finite convex mixtures of unitary conjugations on $\mathbb C^d$. Write $E_{r,k}^c(\mathcal N)$ for the operational parallel block-i.i.d. Stein exponent against this composite i.i.d. null class, in bits, with a uniform Type-I constraint, local reference dimension $r$, and the zero-error outer limit taken after the block-count liminf and limsup. The value $r=1$ means no memory and $r=d$ supplies sufficient memory. Let $\mathcal N$ be a qutrit CPTP channel unitarily equivalent to $\mathcal N_{WH}(X)=(\operatorname{Tr}(X)I-X^T)/2$, with independent input and output unitaries. Then $$E_{1,3}^{\mathrm{product}}(\mathcal N)>0.$$ Three product inputs suffice. This makes no minimality assertion about three.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 25, Theorem 5: three product probes suffice for the qutrit Werner-Holevo channel

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF pp.25–26, Theorem 5, Eq.(75); no minimality assertion. -/
theorem three_product_positive (N : Maps 3 3) (hN : IsChannel N)
    (he : UnitaryEquivalent (wernerHolevo 3) N) : 0 < blockExponent 1 (MU 3) N 3 .product := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
