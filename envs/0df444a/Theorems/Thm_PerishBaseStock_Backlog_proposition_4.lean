-- Prove2me | Theorems.Thm_PerishBaseStock_Backlog_proposition_4
-- name    : PerishBaseStock.Backlog.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:23.936617+00:00
-- url     : https://prove2.me/theorems/3a4901ce-d027-45c6-b7c5-1dad9b133cb7
-- title:
--   Proposition 4 — $\mathrm{OPT}^L\ge\widetilde C^L(\widetilde S^L)$ for lead times $L\ge1$
-- statement:
--   Consider the perishable backlogging system with lifetime $m\ge1$, positive lead time $L\ge1$, costs $h,b>0$ and $\theta\ge hL$, under FIFO issuance, starting empty. Let $\widetilde S^L$ be any minimizer of $\widetilde C^L$ over $[0,\infty)$. Then the optimal long-run average cost over all admissible policies satisfies
--
--   $$\mathrm{OPT}^L\ \ge\ \widetilde C^L(\widetilde S^L).$$
--
--   The minimum value of the explicit function $\widetilde C^L$ is a lower bound on the optimal cost of a system whose optimal policy depends on the whole $(m+L-1)$-dimensional state.
--
--   **Formalization Note** The paper states the result "under any issuance policy"; the backlogging model is specified only for FIFO (p. 19), so FIFO is formalized. $\widetilde C^L(\widetilde S^L)$ is embedded with `ENNReal.ofReal`.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 23, Proposition 4 (proof p. ec13, App. E.2)

import Definitions.Def_PerishBaseStock_Backlog_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Backlog

/-- Proposition 4, p. 23 (FIFO issuance): for `L ≥ 1`, `OPT^L ≥ C̃^L(S̃^L)`. -/
theorem proposition_4 (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (hL : 1 ≤ c.L) (S : ℝ≥0) (hS : IsHeuristicLevel P c S) :
    ENNReal.ofReal (heuristicCost P c S) ≤ OPT P c := by sorry

end PerishBaseStock.Backlog
