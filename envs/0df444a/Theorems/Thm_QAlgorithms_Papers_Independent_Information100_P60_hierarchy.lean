-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_hierarchy
-- name    : QAlgorithms.Papers.Independent.Information100.P60.hierarchy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:37:26.175828+00:00
-- url     : https://prove2.me/theorems/77ecffe3-9d87-4824-90b1-a67a7bb75213
-- title:
--   Sec.IV C, unnumbered: hierarchy inequalities (45)-(50)
-- statement:
--   Let $A=\mathbb C^a$ and $B=\mathbb C^b$, with $a,b>0$, let $\mathcal R$ be a nonempty closed convex set of CPTP maps from $A$ to $B$, and let $\mathcal N\notin\mathcal R$ be CPTP. All relative entropies are in bits, ordered as null output versus alternative output. Every channel use applies the same unknown channel independently. Tests accept the null and constrain Type-I error uniformly over $\mathcal R$. Write $E_{r,k}^c$ for the operational BIID exponent with local reference dimension $r$, block size $k\ge1$, and correlation class $c$ (unrestricted, separable across uses, or product). The entire block repeats independently, with a joint final measurement. Here $r=1$ denotes no memory and $r=a$ suffices for memory assistance. Write $E_{r,\mathrm{arb}}^c$ for the independently defined arbitrary parallel-probe exponent. Exponents take values in $[0,\infty]$, and both outer limits of the inner liminf and limsup are understood as the Type-I tolerance decreases to zero. For every correlation class $c$, $$E_{1,k}^c\le E_{a,k}^c.$$ For $r\in\{1,a\}$ and positive integers $\ell$, $$E_{r,1}^{\mathrm{unrestricted}}\le E_{r,k}^{\mathrm{unrestricted}}\le E_{r,\mathrm{arb}}^{\mathrm{unrestricted}},\qquad E_{r,k}^{\mathrm{unrestricted}}\le E_{r,\ell k}^{\mathrm{unrestricted}},$$ and $$E_{r,k}^{\mathrm{product}}\le E_{r,k}^{\mathrm{separable}}\le E_{r,k}^{\mathrm{unrestricted}}.$$ These are the non-strict operational hierarchy inequalities; zero-sized blocks and arbitrary adjacent-block monotonicity are not asserted.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 15, Sec.IV C, unnumbered: hierarchy inequalities (45)-(50)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF pp.15–16, Sec.IV C, Eqs.(45)–(50); positive multiples only. -/
theorem hierarchy {a b : ℕ} (R : Set (Maps a b)) (N : Maps a b)
    (h : Setting R N) (k : ℕ) (hk : 0 < k) :
    (∀ c, blockExponent 1 R N k c ≤ blockExponent a R N k c) ∧
    (∀ r ∈ ({1, a} : Set ℕ),
      (blockExponent r R N 1 .unrestricted ≤ blockExponent r R N k .unrestricted ∧
       blockExponent r R N k .unrestricted ≤ arbitraryExponent r R N .unrestricted) ∧
      (∀ ell, 0 < ell → blockExponent r R N k .unrestricted ≤ blockExponent r R N (ell * k) .unrestricted) ∧
      blockExponent r R N k .product ≤ blockExponent r R N k .separable ∧
      blockExponent r R N k .separable ≤ blockExponent r R N k .unrestricted) := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
