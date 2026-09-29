-- Prove2me | Theorems.Thm_SchinzelHypothesisH_primes_sq_add_one_of_hypothesis_H
-- name    : SchinzelHypothesisH.primes_sq_add_one_of_hypothesis_H
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T04:35:51.860087+00:00
-- url     : https://prove2.me/theorems/82ae9ee7-1a04-44a1-9b79-2053292bea75
-- title:
--   Hypothesis H implies Landau's problem on $n^2+1$
-- statement:
--   **Landau's fourth problem from Hypothesis H.** Assume Hypothesis H in the same form as above. Then $n^2 + 1$ is prime for infinitely many natural numbers $n$.
--
--   The deduction is the case $\mathcal{F} = \{X^2 + 1\}$: the polynomial is irreducible in $\mathbb{Z}[X]$ with leading coefficient $1$, and it has no fixed prime divisor (for any prime $p$, the value at $n = 0$ is $1$). Unconditionally, the best known result in this direction is Iwaniec's theorem that $n^2+1$ has at most two prime factors infinitely often.
-- source:
--   Landau's fourth problem; the case $\{X^2+1\}$ of Schinzel–Sierpiński, Acta Arith. 4 (1958), 185–208, Hypothesis H

import Definitions.Def_SchinzelHypothesisH_core

namespace SchinzelHypothesisH

theorem primes_sq_add_one_of_hypothesis_H
    (H : ∀ fs : Finset (Polynomial ℤ), (∀ f ∈ fs, BunyakovskyCondition f) →
      SchinzelCondition fs → (PrimeValueSet fs).Infinite) :
    {n : ℕ | (n ^ 2 + 1).Prime}.Infinite := by sorry

end SchinzelHypothesisH
