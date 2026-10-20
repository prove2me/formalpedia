-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_biid_stein
-- name    : QAlgorithms.Papers.Independent.Information100.P60.biid_stein
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:31:39.288928+00:00
-- url     : https://prove2.me/theorems/00b9b182-06be-4f1b-8439-280c1d7cd644
-- title:
--   Theorem 1 (seed paper result): finite-letter BIID_k Stein exponents
-- statement:
--   Let $A=\mathbb C^a$ and $B=\mathbb C^b$, with $a,b>0$, let $\mathcal R$ be a nonempty closed convex set of CPTP maps from $A$ to $B$, and let $\mathcal N\notin\mathcal R$ be CPTP. All relative entropies are in bits, ordered as null output versus alternative output. Every channel use applies the same unknown channel independently. Tests accept the null and constrain Type-I error uniformly over $\mathcal R$. Write $E_{r,k}^c$ for the operational BIID exponent with local reference dimension $r$, block size $k\ge1$, and correlation class $c$ (unrestricted, separable across uses, or product). The entire block repeats independently, with a joint final measurement. Here $r=1$ denotes no memory and $r=a$ suffices for memory assistance. Write $E_{r,\mathrm{arb}}^c$ for the independently defined arbitrary parallel-probe exponent. Exponents take values in $[0,\infty]$, and both outer limits of the inner liminf and limsup are understood as the Type-I tolerance decreases to zero. For a block state $\sigma$, set $\sigma_\Phi=(\operatorname{id}_{r^k}\otimes\Phi^{\otimes k})(\sigma)$ and define $$F_{r,k}^c=\sup_{\sigma\in\mathcal P_{r,k}^c}\frac1k\inf_{\Phi\in\mathcal R}D(\sigma_\Phi\Vert\sigma_{\mathcal N}).$$ Here $\mathcal P_{r,k}^c$ consists of normalized density operators in the specified correlation class. For each $k\ge1$ and $r\in\{1,a\}$, $$E_{r,k}^{\mathrm{unrestricted}}=F_{r,k}^{\mathrm{unrestricted}}.$$ Both outer limiting values exist and equal this expression, and the inner infimum is attained for every probe. This characterizes the operational finite-block exponents.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 11, Theorem 1 (seed paper result): finite-letter BIID_k Stein exponents

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF pp.11–13, Theorem 1, Eqs.(26)–(27); reference dimension a^k suffices. -/
theorem biid_stein {a b : ℕ} (R : Set (Maps a b)) (N : Maps a b)
    (h : Setting R N) (k : ℕ) (hk : 0 < k) :
    FiniteLetter a R N k .unrestricted ∧ FiniteLetter 1 R N k .unrestricted := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
