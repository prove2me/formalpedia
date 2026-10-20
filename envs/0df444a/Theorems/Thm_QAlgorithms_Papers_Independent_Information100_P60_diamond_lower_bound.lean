-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_diamond_lower_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P60.diamond_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:45:17.23598+00:00
-- url     : https://prove2.me/theorems/da029209-666d-432a-a9cf-7cad91d3c59a
-- title:
--   Theorem 7: universal memory-assisted diamond-distance lower bound
-- statement:
--   Let $\mathrm{MU}_d$ be the finite convex mixtures of unitary conjugations on $\mathbb C^d$. Write $E_{r,k}^c(\mathcal N)$ for the operational parallel block-i.i.d. Stein exponent against this composite i.i.d. null class, in bits, with a uniform Type-I constraint, local reference dimension $r$, and the zero-error outer limit taken after the block-count liminf and limsup. The value $r=1$ means no memory and $r=d$ supplies sufficient memory. Let $d>0$ and let $\mathcal N$ be CPTP outside $\mathrm{MU}_d$. Set $\delta=\min_{\Phi\in\mathrm{MU}_d}\|\Phi-\mathcal N\|_\diamond$, with the full stabilized induced trace norm and no factor $1/2$. The minimum is attained, and $$E_{d,1}^{\mathrm{unrestricted}}(\mathcal N)\ge\frac{\delta^2}{2\ln2}>0.$$ This gives a universal positive memory-assisted bound without unitality assumptions.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 31, Theorem 7: universal memory-assisted diamond-distance lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF p.31, Theorem 7, Eq.(126); square outside the minimum. -/
theorem diamond_lower_bound (d : ℕ) (hd : 0 < d) (N : Maps d d)
    (hN : IsChannel N) (hn : N ∉ MU d) :
    let bound := (diamondDistance d hd N)^2 / (2 * Real.log 2)
    0 < bound ∧ ENNReal.ofReal bound ≤ blockExponent d (MU d) N 1 .unrestricted ∧
    ∃ Phi ∈ MU d, IntrinsicLearning.diamondNorm d hd (Phi.toLinearMap - N.toLinearMap) = diamondDistance d hd N := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
