-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_qubit_overlap
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.qubit_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:10:03.915921+00:00
-- url     : https://prove2.me/theorems/efb1eaa4-f605-41fd-aea7-37766f4b2ba0
-- title:
--   Lemma 9: qubit overlap as a finite binomial sum
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. For $d=2$, let $k=\lfloor(N-1)/2\rfloor$ and
--   $$B_{N,l}=(N-2l+1)\sqrt{\frac{\binom{N+1}{l}}{N+1}}+(N-2l-1)\sqrt{\frac{\binom{N+1}{l+1}}{N+1}},\qquad Q_N=\sum_{l=0}^k\sqrt{\frac{(N+1-l)(l+1)}{N+1}}B_{N,l}^2.$$
--   All subtractions in these coefficients are real subtractions. For every selected port $a$,
--   $$\operatorname{Tr}_H(\sqrt{\Pi_a}V_a^\prime)=Q_N/N.$$
--   This is the finite binomial form of the full overlap.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 12, Lemma 9: qubit overlap as a finite binomial sum

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF pp.12-13, Lemma 9, (58),(72): k=floor((N-1)/2), including the terminal zero successor. -/
theorem qubit_overlap (n : ℕ) (a : Fin (n + 1)) :
    (positiveRoot (supportEffect 2 (n + 1) a) * transposedSwap 2 (n + 1) a).trace =
      (qubitOverlapSum n / (n + 1 : ℝ) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
