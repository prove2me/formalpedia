-- Prove2me | Theorems.Thm_ShapleyScarf_TopTrading_affordable_iff_later_stage
-- name    : ShapleyScarf.TopTrading.affordable_iff_later_stage
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:25.261424+00:00
-- url     : https://prove2.me/theorems/30875209-821a-451f-a8be-6f5b3daf3b7a
-- title:
--   Section 6, proof of (2), p. 114 — under cycle prices a trader cannot afford goods of earlier cycles
-- statement:
--   Let $N = S^1 \cup \cdots \cup S^p$ be a top-trading-cycle partition of a housing market, with cyclic successor map $\mathrm{next}$, and assign prices
--   $$\pi^1 > \pi^2 > \cdots > \pi^p > 0$$
--   to the goods of the respective cycles $S^1, \dots, S^p$. Then for every trader $i \in S^j$:
--
--   1. the item of his cyclic successor costs exactly what his own item sells for, $\pi^j$;
--   2. every item he can afford (price at most $\pi^j$) belongs to $S^j \cup S^{j+1} \cup \cdots \cup S^p$; in particular he cannot afford any item of $S^1, \dots, S^{j-1}$.
--
--   Combined with the defining property of top trading cycles, this shows that buying his successor's item maximizes trader $i$'s utility within his budget.
--
--   **Formalization Note** The price of item $k$ is $\pi^{\mathrm{stage}(k)}$, with $\pi$ indexed by `Fin p` from $0$ and the strict decrease written as `StrictAnti π`. Clause 2 is the explicit content of "He cannot afford any items from $S^1,\dots,S^{j-1}$": an item whose price is at most $\pi^j$ has stage at least $j$. Positivity of the prices is carried as on the page, although it is not needed.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974); p. 114 of the source printing, Section 6, proof of assertion (2)

import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle

namespace ShapleyScarf.TopTrading

/-- §6, proof of (2), p. 114: with prices `π¹ > π² > ⋯ > πᵖ > 0` on the goods of the cycles
`S¹, …, Sᵖ`, the item of a trader's cyclic successor costs exactly what his own item sells for,
and every item he can afford lies in his own cycle or a later one. -/
theorem affordable_iff_later_stage {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (P : TTCPartition A) (π : Fin P.p → ℝ) (hπ : StrictAnti π)
    (hπpos : ∀ j, 0 < π j) (i : N) :
    π (P.stage (P.next i)) = π (P.stage i) ∧
      ∀ k, π (P.stage k) ≤ π (P.stage i) → P.stage i ≤ P.stage k := by sorry

end ShapleyScarf.TopTrading
