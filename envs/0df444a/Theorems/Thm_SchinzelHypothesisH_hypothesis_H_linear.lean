-- Prove2me | Theorems.Thm_SchinzelHypothesisH_hypothesis_H_linear
-- name    : SchinzelHypothesisH.hypothesis_H_linear
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T03:57:46.319475+00:00
-- url     : https://prove2.me/theorems/cdf4dc58-6e0a-4c9c-8a35-05cba0986d8a
-- title:
--   Dirichlet: Hypothesis H for one linear polynomial
-- statement:
--   **Dirichlet's theorem on primes in arithmetic progressions (1837), in the shape of Hypothesis H.** Let $a, b$ be integers with $a > 0$ and $a, b$ coprime (i.e. $ax + by = 1$ is solvable in integers). Then $|an + b|$ is prime for infinitely many natural numbers $n$.
--
--   This is exactly the case of Hypothesis H in which $\mathcal{F} = \{aX + b\}$ consists of a single polynomial of degree one: coprimality of $a$ and $b$ is what makes $aX+b$ irreducible in $\mathbb{Z}[X]$ and rules out a fixed prime divisor. It is the only case of Hypothesis H that is known unconditionally.
-- source:
--   Dirichlet's theorem on arithmetic progressions (1837); the linear case of Schinzel–Sierpiński, Acta Arith. 4 (1958), 185–208, Hypothesis H

import Definitions.Def_SchinzelHypothesisH_core

namespace SchinzelHypothesisH

theorem hypothesis_H_linear (a b : ℤ) (ha : 0 < a) (hab : IsCoprime a b) :
    {n : ℕ | (a * (n : ℤ) + b).natAbs.Prime}.Infinite := by sorry

end SchinzelHypothesisH
