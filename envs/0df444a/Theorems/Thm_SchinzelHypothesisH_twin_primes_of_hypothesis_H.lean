-- Prove2me | Theorems.Thm_SchinzelHypothesisH_twin_primes_of_hypothesis_H
-- name    : SchinzelHypothesisH.twin_primes_of_hypothesis_H
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T04:22:20.619488+00:00
-- url     : https://prove2.me/theorems/eac8de62-a560-4622-ab46-d32ae36c7466
-- title:
--   Hypothesis H implies the twin prime conjecture
-- statement:
--   **Twin primes from Hypothesis H.** Assume Hypothesis H, in the form: for every finite set $\mathcal{F} \subseteq \mathbb{Z}[X]$ of non-constant polynomials with positive leading coefficients, irreducible in $\mathbb{Z}[X]$, such that no prime divides $\prod_{f \in \mathcal{F}} f(n)$ for all integers $n$, there are infinitely many natural $n$ at which every $|f(n)|$ is prime.
--
--   Then there are infinitely many primes $p$ such that $p + 2$ is also prime. The deduction is the case $\mathcal{F} = \{X,\; X + 2\}$, which requires checking that both polynomials are irreducible with positive leading coefficient and that $n(n+2)$ has no fixed prime divisor (for $p = 2$ take $n = 1$; for odd $p$ take $n = 1$ unless $p \mid 3$, and so on).
-- source:
--   Twin prime conjecture as the case $\{X, X+2\}$ of Schinzel–Sierpiński, Acta Arith. 4 (1958), 185–208, Hypothesis H

import Definitions.Def_SchinzelHypothesisH_core

namespace SchinzelHypothesisH

theorem twin_primes_of_hypothesis_H
    (H : ∀ fs : Finset (Polynomial ℤ), (∀ f ∈ fs, BunyakovskyCondition f) →
      SchinzelCondition fs → (PrimeValueSet fs).Infinite) :
    {p : ℕ | p.Prime ∧ (p + 2).Prime}.Infinite := by sorry

end SchinzelHypothesisH
