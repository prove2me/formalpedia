-- Prove2me | Theorems.Thm_SchinzelHypothesisH_hypothesis_H
-- name    : SchinzelHypothesisH.hypothesis_H
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T03:50:45.223476+00:00
-- url     : https://prove2.me/theorems/60d4882d-985f-497d-9a9c-92395307814b
-- title:
--   Schinzel's Hypothesis H
-- statement:
--   **Schinzel's Hypothesis H (Schinzel–Sierpiński, 1958).** Let $\mathcal{F}$ be a finite set of polynomials with integer coefficients such that
--
--   1. every $f \in \mathcal{F}$ has degree at least $1$, positive leading coefficient, and is irreducible in $\mathbb{Z}[X]$; and
--   2. for every prime $p$ there is an integer $n$ with $p \nmid \prod_{f \in \mathcal{F}} f(n)$.
--
--   Then there are infinitely many natural numbers $n$ such that $|f(n)|$ is prime for every $f \in \mathcal{F}$ simultaneously.
--
--   Both hypotheses are necessary: a reducible $f$ takes prime values only finitely often, and if some prime $p$ divides $\prod_{f} f(n)$ for all $n$ then some value must equal $\pm p$ at all but finitely many admissible $n$.
-- source:
--   A. Schinzel, W. Sierpinski, Sur certaines hypotheses concernant les nombres premiers, Acta Arithmetica 4 (1958), 185-208, Hypothesis H (p. 188); https://doi.org/10.4064/aa-4-3-185-208

import Definitions.Def_SchinzelHypothesisH_core

namespace SchinzelHypothesisH

theorem hypothesis_H (fs : Finset (Polynomial ℤ))
    (hB : ∀ f ∈ fs, BunyakovskyCondition f) (hS : SchinzelCondition fs) :
    (PrimeValueSet fs).Infinite := by sorry

end SchinzelHypothesisH
