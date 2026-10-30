-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_nonoptimal_le_one
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.nonoptimal_le_one
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:11:19.868496+00:00
-- url     : https://prove2.me/theorems/8f40e2dc-9f06-4a68-b18d-179ca316daea
-- title:
--   Remark 11: recycling fidelity upper bound
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. Here $F_{\rm rec}$ is the Born-weighted average of the unsquared absolute overlaps of normalized whole output branches with the ideal state, retaining the teleported Bell pair and all unused ports. The measurement instrument is $\sqrt{\widetilde\Pi_a}$; $F_{\rm non}$ uses identity resource operations. The one-round unoptimized recycling fidelity satisfies
--   $$F_{\rm non}(N,d)\le1.$$
--   The uniform full-effect trace used in the source proof is a consequence, not an assumption.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 14, Remark 11: recycling fidelity upper bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF pp.14-15, Remark 11, (77): the actual operational fidelity is at most one.
Uniform POVM traces are derived by the paper, not assumed as a hypothesis. -/
theorem nonoptimal_le_one (d n : ℕ) (hd : 2 ≤ d) :
    nonoptimalFidelity d n ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
