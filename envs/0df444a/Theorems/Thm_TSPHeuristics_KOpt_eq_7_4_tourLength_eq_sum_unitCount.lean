-- Prove2me | Theorems.Thm_TSPHeuristics_KOpt_eq_7_4_tourLength_eq_sum_unitCount
-- name    : TSPHeuristics.KOpt.eq_7_4_tourLength_eq_sum_unitCount
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:58:09.547501+00:00
-- url     : https://prove2.me/theorems/f63dd672-6dc7-4fa1-aa58-5b61d8c40199
-- title:
--   (7.4) — on the circle, the length of a tour is $\sum_{e\in E_n}$ COUNT(e, T)
-- statement:
--   On the circle graph $(N_n,d_n)$, every tour $T$ satisfies
--   $$L(T)=\sum_{e\in E_n}\mathrm{COUNT}(e,T),\qquad(7.4)$$
--   because every edge of $T$ is replaced in $\alpha(T)$ by a path of unit edges of the same length.
--
--   This identity converts length comparisons between tours on the circle into comparisons of unit-edge counts, which is how the parity argument of Theorem 6 bounds the effect of a $k$-change.
--
--   **Formalization Note** COUNT uses the canonical arc of the definition `UnitEdgeCount` (shorter arc; the non-wrapping arc in the antipodal tie). The statement holds for every $n$, including the degenerate $n\le 2$.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 580, proof of Theorem 6, eq. (7.4)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance
import Definitions.Def_TSPHeuristics_KOpt_UnitEdgeCount

namespace TSPHeuristics.KOpt

theorem eq_7_4_tourLength_eq_sum_unitCount (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    TSPHeuristics.Shared.tourLength (cycDist n) τ = ∑ e : Fin n, (unitCount τ e : ℝ) := by sorry

end TSPHeuristics.KOpt
