-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_nonoptimal_trace
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.nonoptimal_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:10:46.952048+00:00
-- url     : https://prove2.me/theorems/55dddee6-10fa-4da4-8209-c34db2ba4514
-- title:
--   Lemma 10: operational non-optimal one-round trace formula
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. Here $F_{\rm rec}$ is the Born-weighted average of the unsquared absolute overlaps of normalized whole output branches with the ideal state, retaining the teleported Bell pair and all unused ports. The measurement instrument is $\sqrt{\widetilde\Pi_a}$; $F_{\rm non}$ uses identity resource operations. At the last port,
--   $$F_{\rm non}(N,d)=\frac{N\sqrt{\operatorname{Tr}\widetilde\Pi_N}}{d\sqrt{d^{N+1}}}\left|\operatorname{Tr}(\sigma_N\sqrt{\widetilde\Pi_N})\right|.$$
--   This evaluates the operational average without assuming its trace normalization as a hypothesis.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 14, Lemma 10: operational non-optimal one-round trace formula

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF p.14, Lemma 10, (76), Appendix A pp.19-20: operational unoptimized root fidelity.
The full completed effect is used in both its trace normalization and its square root. -/
theorem nonoptimal_trace (d n : ℕ) (hd : 2 ≤ d) :
    nonoptimalFidelity d n =
      ((n + 1 : ℝ) * Real.sqrt ((fullEffect d (n + 1) (Fin.last n)).trace.re) /
        ((d : ℝ) * Real.sqrt ((d : ℝ) ^ (n + 2)))) *
      ‖(pbtSignal d (n + 1) (Fin.last n) * positiveRoot (fullEffect d (n + 1) (Fin.last n))).trace‖ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
