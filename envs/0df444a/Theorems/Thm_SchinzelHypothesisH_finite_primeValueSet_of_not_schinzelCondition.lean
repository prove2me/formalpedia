-- Prove2me | Theorems.Thm_SchinzelHypothesisH_finite_primeValueSet_of_not_schinzelCondition
-- name    : SchinzelHypothesisH.finite_primeValueSet_of_not_schinzelCondition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T04:12:49.087269+00:00
-- url     : https://prove2.me/theorems/60fd3edc-1bda-4a86-83ea-aa6acd6039d1
-- title:
--   Necessity of the fixed-divisor condition
-- statement:
--   **The Schinzel condition cannot be dropped.** Let $\mathcal{F}$ be a finite set of polynomials in $\mathbb{Z}[X]$, each of degree at least $1$, with positive leading coefficient and irreducible in $\mathbb{Z}[X]$. Suppose the fixed-divisor condition fails, i.e. there is a prime $p$ dividing $\prod_{f \in \mathcal{F}} f(n)$ for every integer $n$. Then only finitely many natural numbers $n$ make $|f(n)|$ prime for all $f \in \mathcal{F}$ simultaneously.
--
--   Indeed, at such an $n$ some value $f(n)$ is divisible by $p$ and has prime absolute value, so $f(n) = \pm p$; each non-constant $f$ attains a given value only finitely often. Together with the goal theorem this shows the hypotheses of Hypothesis H are not merely sufficient but exactly right.
-- source:
--   Schinzel–Sierpiński, Acta Arith. 4 (1958), 185–208 — necessity of the no-fixed-prime-divisor hypothesis

import Definitions.Def_SchinzelHypothesisH_core

namespace SchinzelHypothesisH

theorem finite_primeValueSet_of_not_schinzelCondition (fs : Finset (Polynomial ℤ))
    (hB : ∀ f ∈ fs, BunyakovskyCondition f) (hS : ¬ SchinzelCondition fs) :
    (PrimeValueSet fs).Finite := by sorry

end SchinzelHypothesisH
