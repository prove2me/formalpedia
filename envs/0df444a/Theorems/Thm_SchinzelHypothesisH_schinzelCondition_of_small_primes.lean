-- Prove2me | Theorems.Thm_SchinzelHypothesisH_schinzelCondition_of_small_primes
-- name    : SchinzelHypothesisH.schinzelCondition_of_small_primes
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T04:02:34.972991+00:00
-- url     : https://prove2.me/theorems/0fb43ae7-d8fc-4e04-91b5-0f0daf3e9cea
-- title:
--   The fixed-divisor condition is a finite check
-- statement:
--   **Admissibility is decidable in finitely many steps.** Let $\mathcal{F}$ be a finite set of polynomials in $\mathbb{Z}[X]$, each of degree at least $1$, with positive leading coefficient and irreducible in $\mathbb{Z}[X]$, and put $D = \sum_{f \in \mathcal{F}} \deg f$. If for every prime $p \le D$ there is an integer $n$ with $p \nmid \prod_{f \in \mathcal{F}} f(n)$, then the same holds for every prime.
--
--   The point is that a prime $p > D$ can never be a fixed divisor: each $f$ is primitive, so its reduction modulo $p$ is a nonzero polynomial, hence so is the reduction of the product, and a nonzero polynomial of degree at most $D < p$ over $\mathbb{F}_p$ cannot vanish at all $p$ residues.
-- source:
--   Standard fact about fixed divisors of polynomials; see Schinzel–Sierpiński, Acta Arith. 4 (1958), 185–208, discussion of condition (C)

import Definitions.Def_SchinzelHypothesisH_core

namespace SchinzelHypothesisH

theorem schinzelCondition_of_small_primes (fs : Finset (Polynomial ℤ))
    (hB : ∀ f ∈ fs, BunyakovskyCondition f)
    (h : ∀ p : ℕ, p.Prime → p ≤ ∑ f ∈ fs, f.natDegree →
      ∃ n : ℤ, ¬ ((p : ℤ) ∣ ∏ f ∈ fs, f.eval n)) :
    SchinzelCondition fs := by sorry

end SchinzelHypothesisH
