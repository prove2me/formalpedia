-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_full_overlap
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.full_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:09:30.945012+00:00
-- url     : https://prove2.me/theorems/420f6f7d-aed7-4b34-ad1b-b3443f47e393
-- title:
--   Theorem 8: full Hilbert-space overlap
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. For a Young diagram $\lambda$, write $d_\lambda$ for its symmetric-group irrep dimension and $m_\lambda$ for its Schur–Weyl multiplicity at dimension $d$. Every summed diagram is physical (height at most $d$). For $\alpha\vdash N-1$, put $S_\alpha=\sum_{\nu\supset\alpha,\,\nu\vdash N}\sqrt{m_\nu d_\nu}$ and let $d_\theta$ be the dimension of its unique height-$(d+1)$ successor when $h(\alpha)=d$, zero otherwise. Define
--   $$T_{N,d}=\sum_{h(\alpha)<d}\frac{S_\alpha^2}{N}+\sum_{h(\alpha)=d}\frac{\sqrt{d_\alpha}S_\alpha^2}{\sqrt{Nd_\alpha-d_\theta}\sqrt N}.$$
--   For every $a\in\{1,\ldots,N\}$, on the full Hilbert space $H=(\mathbb C^d)^{\otimes(N+1)}$,
--   $$\operatorname{Tr}_H(\sqrt{\Pi_a}V_a^\prime)=T_{N,d}.$$
--   The trace includes all physical multiplicity copies.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 12, Theorem 8: full Hilbert-space overlap

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF p.12, Theorem 8, (57): overlap on the full N+1-factor Hilbert space. -/
theorem full_overlap (d n : ℕ) (hd : 2 ≤ d) (a : Fin (n + 1)) :
    (positiveRoot (supportEffect d (n + 1) a) * transposedSwap d (n + 1) a).trace =
      (overlapFormula d n : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
