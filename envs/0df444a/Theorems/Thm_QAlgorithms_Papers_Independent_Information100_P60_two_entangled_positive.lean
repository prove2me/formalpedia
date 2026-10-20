-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_two_entangled_positive
-- name    : QAlgorithms.Papers.Independent.Information100.P60.two_entangled_positive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:44:04.51286+00:00
-- url     : https://prove2.me/theorems/97255e9b-d8fb-4562-8991-9da2a0f4cdc1
-- title:
--   Theorem 6: an entangled two-qutrit probe suffices
-- statement:
--   Let $\mathrm{MU}_d$ be the finite convex mixtures of unitary conjugations on $\mathbb C^d$. Write $E_{r,k}^c(\mathcal N)$ for the operational parallel block-i.i.d. Stein exponent against this composite i.i.d. null class, in bits, with a uniform Type-I constraint, local reference dimension $r$, and the zero-error outer limit taken after the block-count liminf and limsup. The value $r=1$ means no memory and $r=d$ supplies sufficient memory. Let $\mathcal N$ be a qutrit CPTP channel unitarily equivalent to $\mathcal N_{WH}(X)=(\operatorname{Tr}(X)I-X^T)/2$. Then $$E_{1,2}^{\mathrm{unrestricted}}(\mathcal N)>0.$$ The entanglement is between two channel inputs, and there is no auxiliary memory. The result is independent of Conjecture 1.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 27, Theorem 6: an entangled two-qutrit probe suffices

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF pp.27–29, Theorem 6, Eq.(94): no auxiliary memory. -/
theorem two_entangled_positive (N : Maps 3 3) (hN : IsChannel N)
    (he : UnitaryEquivalent (wernerHolevo 3) N) : 0 < blockExponent 1 (MU 3) N 2 .unrestricted := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
