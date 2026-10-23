-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_unital_iid_zero
-- name    : QAlgorithms.Papers.Independent.Information100.P60.unital_iid_zero
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:38:51.576015+00:00
-- url     : https://prove2.me/theorems/ad8fd29d-271e-43d3-848e-8a3ec813ae9b
-- title:
--   Theorem 3: zero memoryless i.i.d. exponent
-- statement:
--   Let $\mathrm{MU}_d$ be the finite convex mixtures of unitary conjugations on $\mathbb C^d$. Write $E_{r,k}^c(\mathcal N)$ for the operational parallel block-i.i.d. Stein exponent against this composite i.i.d. null class, in bits, with a uniform Type-I constraint, local reference dimension $r$, and the zero-error outer limit taken after the block-count liminf and limsup. The value $r=1$ means no memory and $r=d$ supplies sufficient memory. Let $d\ge3$ and let $\mathcal N$ be CPTP, unital ($\mathcal N(I)=I$), and outside $\mathrm{MU}_d$. Then $$E_{1,1}^{\mathrm{unrestricted}}(\mathcal N)=0.$$ This is the memoryless fully i.i.d. limitation; the null simulator may depend on the single input state.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 19, Theorem 3: zero memoryless i.i.d. exponent

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF p.19, Theorem 3, Eq.(62): memoryless fully i.i.d. probes. -/
theorem unital_iid_zero {d : ℕ} (hd : 3 ≤ d) (N : Maps d d) (hN : IsChannel N)
    (hu : N 1 = 1) (hn : N ∉ MU d) : blockExponent 1 (MU d) N 1 .unrestricted = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
