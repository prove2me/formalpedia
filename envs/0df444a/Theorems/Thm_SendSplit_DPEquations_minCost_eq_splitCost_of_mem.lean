-- Prove2me | Theorems.Thm_SendSplit_DPEquations_minCost_eq_splitCost_of_mem
-- name    : SendSplit.DPEquations.minCost_eq_splitCost_of_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:39:41.421434+00:00
-- url     : https://prove2.me/theorems/f96c8e46-5f00-4400-8210-30300449b2a0
-- title:
--   Proof of Theorem 2, p. 641 — C_{i{i}} = 0, and C_iI = B_iI whenever i ∈ I
-- statement:
--   Consider a network with arc costs concave on $[0,\infty)$ and vanishing at $0$, and suppose there is a minimum-cost flow for $r$. Then:
--
--   1. $C_{i\{i\}} = 0$ for every node $i$ (the subproblem $i \to \{i\}$ has the zero demand vector, whose minimum cost is zero);
--   2. for every $\emptyset \subset I \subseteq D$ and every $i \in I$,
--   $$C_{iI} \;=\; B_{iI},$$
--   where $B_{iI}$ is computed from the array $C$ itself by (3): for $|I| > 1$, $B_{iI} = \min_{\emptyset \subset J \subset I} [C_{iJ} + C_{i, I \setminus J}]$, and for $|I| = 1$, $B_{iI} = 0$ if $I = \{i\}$ and $+\infty$ otherwise.
--
--   This is the case $i \in I$ of the first part of the proof of Theorem 2: when $i$ itself is a demand node of the subproblem, the splitting term of (2) is attained.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 641, Section 3, proof of Theorem 2

import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem
import Definitions.Def_SendSplit_DPEquations_Equations

namespace SendSplit.DPEquations

theorem minCost_eq_splitCost_of_mem {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (hmin : ∃ x, IsMinCostFlow A c r x) :
    (∀ i : Fin n, minCost A c r i {i} = 0) ∧
      ∀ (i : Fin n) (I : Finset (Fin n)), IsAdmissible r I → i ∈ I →
        minCost A c r i I = splitCost (minCost A c r) i I := by sorry

end SendSplit.DPEquations
