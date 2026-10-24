-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_mu_monotonicity
-- name    : QAlgorithms.Papers.Independent.Information100.P60.mu_monotonicity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:37:58.948507+00:00
-- url     : https://prove2.me/theorems/e316a4a3-bda2-4138-b873-6c482b5887b3
-- title:
--   Theorem 2: monotonicity under MU preprocessing and postprocessing
-- statement:
--   Let $\mathrm{MU}_d$ be the finite convex mixtures of unitary conjugations on $\mathbb C^d$. Write $E_{r,k}^c(\mathcal N)$ for the operational parallel block-i.i.d. Stein exponent against this composite i.i.d. null class, in bits, with a uniform Type-I constraint, local reference dimension $r$, and the zero-error outer limit taken after the block-count liminf and limsup. The value $r=1$ means no memory and $r=d$ supplies sufficient memory. Let $d>0$ and let $\mathcal N,\mathcal M$ be CPTP. Suppose $\mathcal M=\Phi_2\circ\mathcal N\circ\Phi_1$ for $\Phi_1,\Phi_2\in\mathrm{MU}_d$. For all $k\ge1$, $r\in\{1,d\}$, and the three correlation classes $c$, $$E_{r,k}^c(\mathcal M)\le E_{r,k}^c(\mathcal N).$$ If independent input/output unitary conjugations convert $\mathcal N$ to $\mathcal M$, equality holds. The channels may themselves be free. This gives the resource monotonicity and unitary invariance.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 17, Theorem 2: monotonicity under MU preprocessing and postprocessing

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF pp.16–18, Theorem 2, including unitary saturation; MU channels included. -/
theorem mu_monotonicity {d : ℕ} (hd : 0 < d) (N M : Maps d d)
    (hN : IsChannel N) (hM : IsChannel M) (h : MUConvertible N M) (k : ℕ) (hk : 0 < k) :
    ∀ r ∈ ({1, d} : Set ℕ), ∀ c,
      blockExponent r (MU d) M k c ≤ blockExponent r (MU d) N k c ∧
      (UnitaryEquivalent N M → blockExponent r (MU d) M k c = blockExponent r (MU d) N k c) := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
