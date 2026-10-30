-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_nonoptimal_qubit
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.nonoptimal_qubit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:12:02.566785+00:00
-- url     : https://prove2.me/theorems/fe3405f9-45af-46a6-b425-0589b66f78f2
-- title:
--   Lemma 13: qubit non-optimal recycling fidelity
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. Here $F_{\rm rec}$ is the Born-weighted average of the unsquared absolute overlaps of normalized whole output branches with the ideal state, retaining the teleported Bell pair and all unused ports. The measurement instrument is $\sqrt{\widetilde\Pi_a}$; $F_{\rm non}$ uses identity resource operations. For $d=2$, let $k=\lfloor(N-1)/2\rfloor$ and
--   $$B_{N,l}=(N-2l+1)\sqrt{\frac{\binom{N+1}{l}}{N+1}}+(N-2l-1)\sqrt{\frac{\binom{N+1}{l+1}}{N+1}},\qquad Q_N=\sum_{l=0}^k\sqrt{\frac{(N+1-l)(l+1)}{N+1}}B_{N,l}^2.$$
--   All subtractions in these coefficients are real subtractions. The corrected qubit formula is
--   $$F_{\rm non}(N,2)=\frac{Q_N}{\sqrt N\,2^{N+1}}.$$
--   It specializes the general expression using the binomial overlap.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 15, Lemma 13: qubit non-optimal recycling fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF pp.15-16, Lemma 13: corrected (83), with its missing factor 1/N restored.
This follows uniquely by substituting Lemma 9 into (80)/(82); N=n+1. -/
theorem nonoptimal_qubit (n : ℕ) :
    nonoptimalFidelity 2 n = qubitOverlapSum n /
      (Real.sqrt (n + 1 : ℝ) * (2 : ℝ) ^ (n + 2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
