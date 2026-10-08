-- Prove2me | Theorems.Thm_ShapleyScarf_TopTrading_ttc_core_and_competitive
-- name    : ShapleyScarf.TopTrading.ttc_core_and_competitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:04.614728+00:00
-- url     : https://prove2.me/theorems/0fb5329a-44b8-4bff-ad67-e03a4c928113
-- title:
--   Section 6, assertions (1) and (2), p. 114 — the top-trading-cycle allocation is in the core and is competitive
-- statement:
--   Let $N$ be the finite set of traders of a housing market with preference matrix $A = (a_{ij})$, ties allowed. Let
--   $$N = S^1 \cup S^2 \cup \cdots \cup S^p$$
--   be any top-trading-cycle partition ($S^j$ a top trading cycle for $N - (S^1\cup\cdots\cup S^{j-1})$), and let the trades indicated within each cycle be carried out: trader $i = i^j_r \in S^j$ receives the good of his cyclic successor $i^j_{r+1}$, so his payoff is $x_i = a_{i\, i^j_{r+1}}$. Then:
--
--   1. this allocation is a **core allocation**: it is a permutation of the goods, and no nonempty coalition can reshuffle its own goods so that every one of its members is strictly better off;
--   2. it is **competitive** at the prices obtained by assigning arbitrary prices
--   $$\pi^1 > \pi^2 > \cdots > \pi^p > 0$$
--   to the goods of the respective cycles $S^1, \dots, S^p$: each trader can afford his successor's good by selling his own, and no good he can afford is better for him.
--
--   This is David Gale's constructive proof, reported by Shapley and Scarf, that every housing market with indivisible goods has a nonempty core, and moreover a core allocation supported by competitive prices, without any assumption of strict preferences.
--
--   **Formalization Note** Assertion (2) of the paper says that "a set of competitive prices exists"; its proof assigns *arbitrary* prices $\pi^1 > \cdots > \pi^p > 0$, and the statement asserts the result for every such choice, which is stronger than existence. Core allocations and competitive allocations are as in the definition item `ShapleyScarf.TopTrading.Market` (strict improvement for every member of the blocking coalition; budget and optimization clauses for prices). The cycle index of item $k$ is `P.stage k : Fin p`, counted from $0$, and the strict decrease is `StrictAnti π`.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974); p. 114 of the source printing, Section 6, assertions (1) and (2)

import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_Market
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle

namespace ShapleyScarf.TopTrading

/-- §6, assertions (1) and (2), p. 114: for every top-trading-cycle partition, the allocation
that gives each trader the item of his cyclic successor is a core allocation, and it is
competitive at the prices `π^{stage k}` for every choice `π¹ > π² > ⋯ > πᵖ > 0`. -/
theorem ttc_core_and_competitive {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (P : TTCPartition A) :
    IsCoreAllocation A P.next ∧
      ∀ π : Fin P.p → ℝ, StrictAnti π → (∀ j, 0 < π j) →
        IsCompetitive A P.next (fun k => π (P.stage k)) := by sorry

end ShapleyScarf.TopTrading
