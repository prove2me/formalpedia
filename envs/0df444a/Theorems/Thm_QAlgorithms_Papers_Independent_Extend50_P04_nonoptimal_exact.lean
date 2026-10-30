-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_nonoptimal_exact
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.nonoptimal_exact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:08:20.995176+00:00
-- url     : https://prove2.me/theorems/2b7b08fa-ccb9-4d57-bab7-2f920c54dc42
-- title:
--   Theorem 12 / abstract seed: exact non-optimal one-round recycling fidelity
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. Here $F_{\rm rec}$ is the Born-weighted average of the unsquared absolute overlaps of normalized whole output branches with the ideal state, retaining the teleported Bell pair and all unused ports. The measurement instrument is $\sqrt{\widetilde\Pi_a}$; $F_{\rm non}$ uses identity resource operations. For a Young diagram $\lambda$, write $d_\lambda$ for its symmetric-group irrep dimension and $m_\lambda$ for its Schur–Weyl multiplicity at dimension $d$. Every summed diagram is physical (height at most $d$). For $\alpha\vdash N-1$, put $S_\alpha=\sum_{\nu\supset\alpha,\,\nu\vdash N}\sqrt{m_\nu d_\nu}$ and let $d_\theta$ be the dimension of its unique height-$(d+1)$ successor when $h(\alpha)=d$, zero otherwise. Define
--   $$T_{N,d}=\sum_{h(\alpha)<d}\frac{S_\alpha^2}{N}+\sum_{h(\alpha)=d}\frac{\sqrt{d_\alpha}S_\alpha^2}{\sqrt{Nd_\alpha-d_\theta}\sqrt N}.$$
--   The exact one-round formula is
--   $$F_{\rm non}(N,d)=\frac{\sqrt N}{d^{N+1}}T_{N,d}.$$
--   This expresses an operational quantity using finite representation data.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 15, Theorem 12 / abstract seed: exact non-optimal one-round recycling fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF p.15, Theorem 12, (80): exact all-d unoptimized one-round recycling fidelity.
Printed (81) has d^(N+2); (76),(79),(82) require d^(N+1), used here. -/
theorem nonoptimal_exact (d n : ℕ) (hd : 2 ≤ d) :
    nonoptimalFidelity d n = Real.sqrt (n + 1 : ℝ) / (d : ℝ) ^ (n + 2) * overlapFormula d n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
