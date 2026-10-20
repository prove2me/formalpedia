-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_isotropic_positive
-- name    : QAlgorithms.Papers.Independent.Information100.P60.isotropic_positive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:46:15.716878+00:00
-- url     : https://prove2.me/theorems/6a7e9462-4ed5-48fc-8c0d-24a0b5d98934
-- title:
--   Proposition 3: universal isotropic probes, including separable ones
-- statement:
--   Let $\mathrm{MU}_d$ be the finite convex mixtures of unitary conjugations on $\mathbb C^d$. Write $E_{r,k}^c(\mathcal N)$ for the operational parallel block-i.i.d. Stein exponent against this composite i.i.d. null class, in bits, with a uniform Type-I constraint, local reference dimension $r$, and the zero-error outer limit taken after the block-count liminf and limsup. The value $r=1$ means no memory and $r=d$ supplies sufficient memory. Let $d>0$, let $\mathcal N$ be CPTP outside $\mathrm{MU}_d$, and let $0<p\le1$. Define $|\Omega_d\rangle=d^{-1/2}\sum_{j=0}^{d-1}|jj\rangle$ and $\rho(p)=p|\Omega_d\rangle\langle\Omega_d|+(1-p)I_{d^2}/d^2$. This is a density operator and $$\min_{\Phi\in\mathrm{MU}_d}D((\operatorname{id}_d\otimes\Phi)(\rho(p))\Vert(\operatorname{id}_d\otimes\mathcal N)(\rho(p)))>0.$$ Moreover $\rho(p)$ is separable across reference/input whenever $p\le1/(d+1)$, including equality. Thus a universal separable probe can have a positive fixed-probe exponent. The relative-entropy minimum is attained.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 32, Proposition 3: universal isotropic probes, including separable ones

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF p.32, Proposition 3: positivity and inclusive separability threshold. -/
theorem isotropic_positive (d : ℕ) (hd : 0 < d) (N : Maps d d)
    (hN : IsChannel N) (hn : N ∉ MU d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    IsDensityMatrix (isotropic d p) ∧ SingleMinimumAttained N (isotropic d p) ∧
    0 < singleValue N (isotropic d p) ∧
    (p ≤ 1 / (d + 1 : ℝ) → Entanglement.IsSeparablePositive (isotropic d p)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
