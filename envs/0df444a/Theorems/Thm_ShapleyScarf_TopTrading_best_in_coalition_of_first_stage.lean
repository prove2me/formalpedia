-- Prove2me | Theorems.Thm_ShapleyScarf_TopTrading_best_in_coalition_of_first_stage
-- name    : ShapleyScarf.TopTrading.best_in_coalition_of_first_stage
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:28.786423+00:00
-- url     : https://prove2.me/theorems/ba01955c-015a-4b3b-8640-3e8a290d9443
-- title:
--   Section 6, proof of (1), p. 114 — a trader in the first cycle meeting S already gets his best payoff available in S
-- statement:
--   Let $N = S^1 \cup \cdots \cup S^p$ be a top-trading-cycle partition of a housing market with preference matrix $A$, and let $\mathrm{next}(i)$ be trader $i$'s cyclic successor. Let $S$ be a coalition, let $j$ be the first index with $S\cap S^j \ne \emptyset$, and let $i \in S \cap S^j$. Then $S \subseteq S^j \cup \cdots \cup S^p$, and $i$ is already getting the highest payoff available to him in $S$:
--   $$a_{ik} \le a_{i\,\mathrm{next}(i)}\qquad\text{for every } k\in S.$$
--
--   This is the heart of the proof that the cycle allocation is in the core: no member of $S\cap S^j$ can be made strictly better off by trading within $S$.
--
--   **Formalization Note** "The first $j$ such that $S \cap S^j \ne \emptyset$" and "$i \in S\cap S^j$" are expressed by $i \in S$ together with $\mathrm{stage}(i) \le \mathrm{stage}(k)$ for all $k\in S$. "The highest possible payoff available to him in $S$" is read as: the item of his successor is at least as good for him as every item of $S$.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974); p. 114 of the source printing, Section 6, proof of assertion (1)

import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle

namespace ShapleyScarf.TopTrading

/-- §6, proof of (1), p. 114: if `i ∈ S` lies in the first cycle `Sʲ` that meets the coalition
`S` (every member of `S` has stage `≥ j`), then `i` already gets, from his cyclic successor,
the highest payoff available to him from the items of `S`. -/
theorem best_in_coalition_of_first_stage {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (P : TTCPartition A) (S : Finset N) (i : N) (hi : i ∈ S)
    (hfirst : ∀ k ∈ S, P.stage i ≤ P.stage k) :
    ∀ k ∈ S, A i k ≤ A i (P.next i) := by sorry

end ShapleyScarf.TopTrading
