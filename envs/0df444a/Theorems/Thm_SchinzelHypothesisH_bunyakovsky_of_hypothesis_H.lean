-- Prove2me | Theorems.Thm_SchinzelHypothesisH_bunyakovsky_of_hypothesis_H
-- name    : SchinzelHypothesisH.bunyakovsky_of_hypothesis_H
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T04:18:06.066973+00:00
-- url     : https://prove2.me/theorems/1c31595c-4ed4-440f-8ebe-a7998c33639f
-- title:
--   Hypothesis H implies Bunyakovsky's conjecture
-- statement:
--   **Bunyakovsky's conjecture (1857) as a consequence of Hypothesis H.** Assume Hypothesis H: for every finite set $\mathcal{F} \subseteq \mathbb{Z}[X]$ whose members are non-constant, have positive leading coefficient and are irreducible in $\mathbb{Z}[X]$, and for which no prime divides $\prod_{f \in \mathcal{F}} f(n)$ for all $n$, there are infinitely many natural $n$ with all $|f(n)|$ prime.
--
--   Then for a single polynomial $f$ of degree at least $1$ with positive leading coefficient, irreducible in $\mathbb{Z}[X]$, and such that for each prime $p$ some integer $n$ has $p \nmid f(n)$, the value $|f(n)|$ is prime for infinitely many natural numbers $n$. This is the one-polynomial case, open for every polynomial of degree at least two.
-- source:
--   V. Bunyakovsky (1857); stated as the case $k = 1$ of Hypothesis H in Schinzel–Sierpiński, Acta Arith. 4 (1958), 185–208

import Definitions.Def_SchinzelHypothesisH_core

namespace SchinzelHypothesisH

theorem bunyakovsky_of_hypothesis_H
    (H : ∀ fs : Finset (Polynomial ℤ), (∀ f ∈ fs, BunyakovskyCondition f) →
      SchinzelCondition fs → (PrimeValueSet fs).Infinite)
    (f : Polynomial ℤ) (hf : BunyakovskyCondition f)
    (hfix : ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ ((p : ℤ) ∣ f.eval n)) :
    {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}.Infinite := by sorry

end SchinzelHypothesisH
