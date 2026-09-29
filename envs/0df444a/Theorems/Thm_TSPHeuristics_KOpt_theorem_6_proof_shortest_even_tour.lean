-- Prove2me | Theorems.Thm_TSPHeuristics_KOpt_theorem_6_proof_shortest_even_tour
-- name    : TSPHeuristics.KOpt.theorem_6_proof_shortest_even_tour
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:00:18.647635+00:00
-- url     : https://prove2.me/theorems/1e8a2c29-2164-47f0-b0ba-2d7cc33e7c5a
-- title:
--   Proof of Theorem 6 — $T_n$ is the shortest even tour, so any tour improving on $T_n$ is odd
-- statement:
--   Let $n\ge 6$ and consider the circle graph $(N_n,d_n)$ and the subtour $T_n$ of the proof of Theorem 5. Then
--
--   1. for every tour $T$, at most one unit edge $e\in E_n$ has $\mathrm{COUNT}(e,T)=0$;
--   2. every even tour $T$ is at least as long as $T_n$: $\ell(T_n)\le L(T)$;
--   3. every tour $T$ with $L(T)<\ell(T_n)$ is odd.
--
--   Item 2 is "$T_n$ is the shortest even tour" ($T_n$ has one unit edge of count $0$ and all others of count $2$, (7.2)–(7.3)); item 3 is its consequence together with the odd/even dichotomy.
--
--   **Formalization Note** $T_n$ is the list `circleSubtour n n`; tours are permutations. COUNT uses the canonical arc of `UnitEdgeCount`. The counts (7.2)–(7.3) of $T_n$ itself are not stated; item 2 states the length comparison they are used for.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 580, proof of Theorem 6, paragraph 'For any tour T, there can be only one edge e in E_n such that COUNT(e, T) = 0 …'

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance
import Definitions.Def_TSPHeuristics_KOpt_UnitEdgeCount

namespace TSPHeuristics.KOpt

theorem theorem_6_proof_shortest_even_tour (n : ℕ) (hn : 6 ≤ n) :
    (∀ (τ : Equiv.Perm (Fin n)) (e e' : Fin n),
        unitCount τ e = 0 → unitCount τ e' = 0 → e = e') ∧
      (∀ τ : Equiv.Perm (Fin n), (∀ e : Fin n, Even (unitCount τ e)) →
        TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) ≤ TSPHeuristics.Shared.tourLength (cycDist n) τ) ∧
      (∀ τ : Equiv.Perm (Fin n),
        TSPHeuristics.Shared.tourLength (cycDist n) τ < TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) →
          ∀ e : Fin n, Odd (unitCount τ e)) := by sorry

end TSPHeuristics.KOpt
