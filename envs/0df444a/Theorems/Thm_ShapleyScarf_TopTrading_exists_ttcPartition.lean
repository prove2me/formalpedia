-- Prove2me | Theorems.Thm_ShapleyScarf_TopTrading_exists_ttcPartition
-- name    : ShapleyScarf.TopTrading.exists_ttcPartition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:42.354775+00:00
-- url     : https://prove2.me/theorems/f9721d97-20ec-44d0-a5ff-c7d72d239c24
-- title:
--   Section 6, p. 114 — N can be partitioned into successive top trading cycles
-- statement:
--   Let $N$ be the finite set of traders of a housing market with preference matrix $A$ (ties allowed). There is a top-trading-cycle partition
--   $$N = S^1 \cup S^2 \cup \cdots \cup S^p,$$
--   with $S^1$ a top trading cycle for $N$ and each $S^j$ a top trading cycle for $N - (S^1 \cup \cdots \cup S^{j-1})$.
--
--   The existence of such a partition is what makes the main theorem of Section 6 non-vacuous: it yields a core allocation of every market, supported by competitive prices.
--
--   **Formalization Note** Stated as the nonemptiness of the type of partitions (number of cycles, stage map, successor map). For a nonempty market the partition automatically has $p \ge 1$ cycles ("one or more disjoint sets"); for the empty market it is the empty partition.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974); p. 114 of the source printing, Section 6 ('we can partition N into a sequence of one or more disjoint sets')

import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle

namespace ShapleyScarf.TopTrading

/-- §6, p. 114: every market has a top-trading-cycle partition `N = S¹ ∪ ⋯ ∪ Sᵖ`. -/
theorem exists_ttcPartition {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ) :
    Nonempty (TTCPartition A) := by sorry

end ShapleyScarf.TopTrading
