-- Prove2me | Theorems.Thm_ShapleyScarf_TopTrading_exists_topTradingCycle
-- name    : ShapleyScarf.TopTrading.exists_topTradingCycle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:30.355561+00:00
-- url     : https://prove2.me/theorems/bb1cab99-f90e-427c-8931-a1fdbe3505c1
-- title:
--   Section 6, p. 114 — every nonempty set of traders has a top trading cycle
-- statement:
--   Let $N$ be the finite set of traders of a housing market with preference matrix $A$ (ties allowed). For every nonempty $R \subseteq N$ there exist a set $S$ and a cyclic order on $S$ making $S$ a top trading cycle for $R$:
--   $$\emptyset \ne R\subseteq N \;\Longrightarrow\; \exists\, S,\ \text{a top trading cycle for } R.$$
--
--   This is the step that makes Gale's construction possible: it is applied to $N$, then to the traders not yet removed, and so on.
--
--   **Formalization Note** The paper writes "it is evident"; the statement asks for a set $S$ and a successor map witnessing the definition of a top trading cycle (one cycle, contained in $R$, each member's successor's good best in $R$).
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974); p. 114 of the source printing, Section 6 ('every nonempty R ⊆ N has at least one top trading cycle')

import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle

namespace ShapleyScarf.TopTrading

/-- §6, p. 114: every nonempty set of traders `R` has at least one top trading cycle. -/
theorem exists_topTradingCycle {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ)
    (R : Finset N) (hR : R.Nonempty) :
    ∃ (S : Finset N) (next : N → N), IsTopTradingCycle A R S next := by sorry

end ShapleyScarf.TopTrading
