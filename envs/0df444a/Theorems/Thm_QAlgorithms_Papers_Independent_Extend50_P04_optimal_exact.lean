-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_optimal_exact
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.optimal_exact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:12:35.156992+00:00
-- url     : https://prove2.me/theorems/c65d5cdb-256f-4996-abbf-5cfff11220d4
-- title:
--   Theorem 14: optimal one-round group-theoretic fidelity
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. Here $F_{\rm rec}$ is the Born-weighted average of the unsquared absolute overlaps of normalized whole output branches with the ideal state, retaining the teleported Bell pair and all unused ports. The measurement instrument is $\sqrt{\widetilde\Pi_a}$; $F_{\rm non}$ uses identity resource operations. For a Young diagram $\lambda$, write $d_\lambda$ for its symmetric-group irrep dimension and $m_\lambda$ for its Schur–Weyl multiplicity at dimension $d$. Every summed diagram is physical (height at most $d$). For $\alpha\vdash N-1$, put $S_\alpha=\sum_{\nu\supset\alpha,\,\nu\vdash N}\sqrt{m_\nu d_\nu}$ and let $d_\theta$ be the dimension of its unique height-$(d+1)$ successor when $h(\alpha)=d$, zero otherwise. Define
--   $$T_{N,d}=\sum_{h(\alpha)<d}\frac{S_\alpha^2}{N}+\sum_{h(\alpha)=d}\frac{\sqrt{d_\alpha}S_\alpha^2}{\sqrt{Nd_\alpha-d_\theta}\sqrt N}.$$
--   For $r$ ports, let $v^{(r)}$ be nonnegative Euclidean-normalized coefficients selected by maximizing the physical deterministic teleportation objective (6), and set $O_r=d^{r/2}\sum_{\lambda\vdash r}v^{(r)}_\lambda P_\lambda/\sqrt{d_\lambda m_\lambda}$ using the actual central character projectors. At $r=0$ this is the scalar identity. Operators on fewer registers are extended by identities. For the optimized resource and its corresponding ideal unused resource,
--   $$F_{\rm opt}(N,d)=\frac{1}{d\sqrt d}\sum_{\alpha\vdash N-1}\sum_{\mu\supset\alpha,\,\mu\vdash N}\frac{v^{(N-1)}_\alpha v^{(N)}_\mu S_\alpha}{\sqrt{m_\alpha}\sqrt{Nd_\alpha-d_\theta}}.$$
--   This is the group-theoretic form of the operational optimized overlap.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 16, Theorem 14: optimal one-round group-theoretic fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF p.16, Theorem 14: corrected (85), using d^(-3/2) as independently printed in (D13), p.24.
At N=1 the printed d^(-1/2) gives 1 instead of the operational 1/d. -/
theorem optimal_exact (d n : ℕ) (hd : 2 ≤ d)
    (v : Schur.Partition d (n + 1) → ℝ) (w : Schur.Partition d n → ℝ)
    (hv : IsOptimalCoefficients d (n + 1) v) (hw : IsOptimalCoefficients d n w) :
    recyclingFidelity d n (resourceOperation d (n + 1) v) (resourceOperation d n w) =
      (1 / ((d : ℝ) * Real.sqrt d)) * ∑ alpha : Schur.Partition d n,
        ∑ mu : Schur.Partition d (n + 1), if pbtOneBoxSuccessor alpha mu then
          w alpha * v mu * successorSum alpha /
            (Real.sqrt (Schur.schurDimension alpha) *
              Real.sqrt ((n + 1 : ℝ) * irrepDimension alpha - forbiddenDimension alpha)) else 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
