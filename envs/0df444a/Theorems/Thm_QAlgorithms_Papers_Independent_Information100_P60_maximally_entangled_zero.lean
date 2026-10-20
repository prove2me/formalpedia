-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_maximally_entangled_zero
-- name    : QAlgorithms.Papers.Independent.Information100.P60.maximally_entangled_zero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:44:36.461658+00:00
-- url     : https://prove2.me/theorems/97bf439d-a9c6-4ac9-9d6c-828b87dbfcb4
-- title:
--   Proposition 2: every maximally entangled two-qutrit probe fails
-- statement:
--   Let $\mathrm{MU}_d$ be the finite convex mixtures of unitary conjugations on $\mathbb C^d$. Write $E_{r,k}^c(\mathcal N)$ for the operational parallel block-i.i.d. Stein exponent against this composite i.i.d. null class, in bits, with a uniform Type-I constraint, local reference dimension $r$, and the zero-error outer limit taken after the block-count liminf and limsup. The value $r=1$ means no memory and $r=d$ supplies sufficient memory. Let $\mathcal N$ be a qutrit CPTP channel unitarily equivalent to $\mathcal N_{WH}(X)=(\operatorname{Tr}(X)I-X^T)/2$. Restrict each two-use block to $|\Omega_V\rangle=(I\otimes V)|\Omega_3\rangle$, $V\in U(3)$, where $|\Omega_3\rangle=3^{-1/2}\sum_{j=0}^2|jj\rangle$. Both registers pass through the channel. Even optimizing over all such $V$, $$E_{\mathrm{MES}}^2(\mathcal N)=0.$$ This shows that maximal entanglement between the inputs need not help. Both outer limiting values exist and equal zero.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 29, Proposition 2: every maximally entangled two-qutrit probe fails

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF pp.29–30, Proposition 2, Eq.(113): optimize over ALL MES probes. -/
theorem maximally_entangled_zero (N : Maps 3 3) (hN : IsChannel N)
    (he : UnitaryEquivalent (wernerHolevo 3) N) : HasSteinValue (blockRate 1 (MU 3) N 2 (MESProbe 3)) 0 ∧
    operational (blockRate 1 (MU 3) N 2 (MESProbe 3)) = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
