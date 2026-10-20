-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_product_stein
-- name    : QAlgorithms.Papers.Independent.Information100.P60.product_stein
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:35:41.470995+00:00
-- url     : https://prove2.me/theorems/386afd34-f5ab-4567-b839-d095b1e3d31c
-- title:
--   Corollary 1.3: product blocks
-- statement:
--   Let $A=\mathbb C^a$ and $B=\mathbb C^b$, with $a,b>0$, let $\mathcal R$ be a nonempty closed convex set of CPTP maps from $A$ to $B$, and let $\mathcal N\notin\mathcal R$ be CPTP. All relative entropies are in bits, ordered as null output versus alternative output. Every channel use applies the same unknown channel independently. Tests accept the null and constrain Type-I error uniformly over $\mathcal R$. Write $E_{r,k}^c$ for the operational BIID exponent with local reference dimension $r$, block size $k\ge1$, and correlation class $c$ (unrestricted, separable across uses, or product). The entire block repeats independently, with a joint final measurement. Here $r=1$ denotes no memory and $r=a$ suffices for memory assistance. Write $E_{r,\mathrm{arb}}^c$ for the independently defined arbitrary parallel-probe exponent. Exponents take values in $[0,\infty]$, and both outer limits of the inner liminf and limsup are understood as the Type-I tolerance decreases to zero. For a block state $\sigma$, set $\sigma_\Phi=(\operatorname{id}_{r^k}\otimes\Phi^{\otimes k})(\sigma)$ and define $$F_{r,k}^c=\sup_{\sigma\in\mathcal P_{r,k}^c}\frac1k\inf_{\Phi\in\mathcal R}D(\sigma_\Phi\Vert\sigma_{\mathcal N}).$$ Here $\mathcal P_{r,k}^c$ consists of normalized density operators in the specified correlation class. For product blocks and $r\in\{1,a\}$, $$E_{r,k}^{\mathrm{product}}=\frac1k\sup_{\tau_1,\ldots,\tau_k\in\mathcal D(\mathbb C^r\otimes A)}\min_{\Phi\in\mathcal R}\sum_{i=1}^kD((\operatorname{id}_r\otimes\Phi)(\tau_i)\Vert(\operatorname{id}_r\otimes\mathcal N)(\tau_i)).$$ Both operational outer limits agree and the minimum is attained. One channel must fit all factors; the factors may differ. This gives a finite-letter product-probe characterization.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 14, Corollary 1.3: product blocks

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF p.14, Corollary 1.3, Eqs.(39)–(40); one channel minimizes the sum. -/
theorem product_stein {a b : ℕ} (R : Set (Maps a b)) (N : Maps a b)
    (h : Setting R N) (k : ℕ) (hk : 0 < k) : ∀ r ∈ ({1, a} : Set ℕ),
      FiniteLetter r R N k .product ∧ blockExponent r R N k .product = productValue r R N k := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
