-- Prove2me | Theorems.Thm_PerishBaseStock_Lifo_proposition_2
-- name    : PerishBaseStock.Lifo.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:12.413029+00:00
-- url     : https://prove2.me/theorems/4d606c68-65ac-46f5-bce4-1934cf268781
-- title:
--   Proposition 2 (LIFO instance) — $\mathrm{OPT}^{LIFO}\ge\widetilde C(\widetilde S)$
-- statement:
--   In the LIFO perishable inventory system with lifetime $m\ge 1$ and costs $h>0$, $p>0$, $\theta\ge 0$, let $\widetilde S$ be any minimizer over $[0,\infty)$ of
--   $$\widetilde C(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\frac{\theta}{m}\mathbb E\Big[\Big(S-\sum_{i=1}^mD_i\Big)^+\Big].$$
--   Then the optimal long-run average cost over all admissible policies satisfies
--   $$\mathrm{OPT}^{LIFO}\ge\widetilde C(\widetilde S).$$
--
--   This is the lower bound on the optimal cost against which every gap in Theorem 5 is measured.
--
--   **Formalization Note** The paper states Proposition 2 "under any issuance policy"; this item formalizes it for the LIFO system only (the FIFO instance is posed in mission 1 of this series). $\mathrm{OPT}^{LIFO}$ is the infimum over all measurable state-feedback policies, in $[0,\infty]$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 21, Proposition 2 (LIFO instance)

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.Lifo

/-- Proposition 2, LIFO instance: `OPT^{LIFO} ≥ C̃(S̃)` for every minimizer `S̃` of `C̃`. -/
theorem proposition_2 (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (St : ℝ≥0) (hSt : IsTildeMinimizer P c St) :
    ENNReal.ofReal (tildeC P c St) ≤ OPT P c := by sorry

end PerishBaseStock.Lifo
