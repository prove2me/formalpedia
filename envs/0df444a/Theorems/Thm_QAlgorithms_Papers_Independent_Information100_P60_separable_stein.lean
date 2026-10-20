-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_separable_stein
-- name    : QAlgorithms.Papers.Independent.Information100.P60.separable_stein
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:34:36.449567+00:00
-- url     : https://prove2.me/theorems/c7d1de34-766f-4a66-9347-62e53d4a9753
-- title:
--   Sec.IV B, unnumbered: finite-letter formulas for fully separable blocks
-- statement:
--   Let $A=\mathbb C^a$ and $B=\mathbb C^b$, with $a,b>0$, let $\mathcal R$ be a nonempty closed convex set of CPTP maps from $A$ to $B$, and let $\mathcal N\notin\mathcal R$ be CPTP. All relative entropies are in bits, ordered as null output versus alternative output. Every channel use applies the same unknown channel independently. Tests accept the null and constrain Type-I error uniformly over $\mathcal R$. Write $E_{r,k}^c$ for the operational BIID exponent with local reference dimension $r$, block size $k\ge1$, and correlation class $c$ (unrestricted, separable across uses, or product). The entire block repeats independently, with a joint final measurement. Here $r=1$ denotes no memory and $r=a$ suffices for memory assistance. Write $E_{r,\mathrm{arb}}^c$ for the independently defined arbitrary parallel-probe exponent. Exponents take values in $[0,\infty]$, and both outer limits of the inner liminf and limsup are understood as the Type-I tolerance decreases to zero. For a block state $\sigma$, set $\sigma_\Phi=(\operatorname{id}_{r^k}\otimes\Phi^{\otimes k})(\sigma)$ and define $$F_{r,k}^c=\sup_{\sigma\in\mathcal P_{r,k}^c}\frac1k\inf_{\Phi\in\mathcal R}D(\sigma_\Phi\Vert\sigma_{\mathcal N}).$$ Here $\mathcal P_{r,k}^c$ consists of normalized density operators in the specified correlation class. For separable blocks, $\mathcal P_{r,k}^{\mathrm{separable}}$ consists of states $\sigma=\sum_jp_j\bigotimes_{i=1}^k\tau_i^j$, where $(p_j)$ is a finite probability vector and every $\tau_i^j$ is a density operator on $\mathbb C^r\otimes A$. Thus entanglement within a reference/input pair is allowed. For $r\in\{1,a\}$, $$E_{r,k}^{\mathrm{separable}}=F_{r,k}^{\mathrm{separable}}.$$ The inner minima are attained and both operational outer limits agree. For either separable or product constraints $c$, the independently defined arbitrary-probe exponent satisfies $$E_{r,\mathrm{arb}}^c=\lim_{k\to\infty}F_{r,k}^c.$$ This retains the constrained regularization statement.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 14, Sec.IV B, unnumbered: finite-letter formulas for fully separable blocks

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF p.14, Sec.IV B: Eq.(37) restrictions and constrained regularization. -/
theorem separable_stein {a b : ℕ} (R : Set (Maps a b)) (N : Maps a b)
    (h : Setting R N) :
    (∀ k, 0 < k → FiniteLetter a R N k .separable ∧ FiniteLetter 1 R N k .separable) ∧
    (∀ r ∈ ({1, a} : Set ℕ), ∀ c ∈ ({Correlation.separable, Correlation.product} : Set Correlation),
      HasSteinValue (arbitraryRate r R N c) (arbitraryExponent r R N c) ∧
      Tendsto (fun k => finiteValue r R N (k + 1) c) atTop (𝓝 (arbitraryExponent r R N c))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
