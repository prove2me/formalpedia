-- Prove2me | Theorems.Thm_TSPHeuristics_KOpt_theorem_6_proof_tour_odd_or_even
-- name    : TSPHeuristics.KOpt.theorem_6_proof_tour_odd_or_even
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:58:51.357976+00:00
-- url     : https://prove2.me/theorems/d31d5487-5a6a-40b5-9f91-46228e1667a2
-- title:
--   Proof of Theorem 6 — every tour on the circle is odd or even
-- statement:
--   Let $n\ge 3$. Call a tour $T$ of the circle graph $(N_n,d_n)$ **even** if $\mathrm{COUNT}(e,T)$ is even for every unit edge $e\in E_n$, and **odd** if it is odd for every $e\in E_n$. Then every tour is either even or odd.
--
--   The reason is (7.5): at each node $a$ the two unit edges $(a,a+1)$ and $(a,a-1)$ have counts summing to twice the number of visits of $\alpha(T)$ to $a$, and $E_n$ is connected.
--
--   The dichotomy is the key step of Theorem 6: a tour shorter than $T_n$ must switch the parity of every unit edge.
--
--   **Formalization Note** Nodes are 0-based and unit edge $e$ joins $e$ and $e+1 \bmod n$. COUNT uses the canonical arc of `UnitEdgeCount`. The hypothesis $n\ge 3$ keeps $E_n$ a cycle of $n$ distinct edges.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 580, proof of Theorem 6, definition of odd and even tours and (7.5)

import Mathlib
import Definitions.Def_TSPHeuristics_KOpt_UnitEdgeCount

namespace TSPHeuristics.KOpt

theorem theorem_6_proof_tour_odd_or_even (n : ℕ) (hn : 3 ≤ n) (τ : Equiv.Perm (Fin n)) :
    (∀ e : Fin n, Even (unitCount τ e)) ∨ (∀ e : Fin n, Odd (unitCount τ e)) := by sorry

end TSPHeuristics.KOpt
