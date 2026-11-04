-- Prove2me | Theorems.Thm_PerishBaseStock_Penalty_proposition_3
-- name    : PerishBaseStock.Penalty.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:31.182118+00:00
-- url     : https://prove2.me/theorems/b93e1d70-7672-4152-a04a-c630a006cfc3
-- title:
--   Proposition 3: with bounded demand, $\mathrm{OPT}\ge h\mathbb E[(\underline S-D)^+]+\theta\mathbb E[O_\infty(\underline S)]$
-- statement:
--   Consider the lost-sales perishable inventory system with lifetime $m\ge1$, zero lead time and FIFO issuance, with costs $h>0$, $p>0$, $\theta\ge0$ and i.i.d. demands with $0<\mathbb E[D]<\infty$. Suppose that demand is bounded, $\bar D<\infty$. Let
--
--   $$\underline S=\arg\min_{S\ge0}\{h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\theta S\}$$
--
--   (the least minimizer), and let $\mathbb E[O_\infty(\underline S)]$ be the long-run average outdated quantity of the base-stock policy $\pi_{\underline S}$. Then the optimal long-run average cost satisfies
--
--   $$\mathrm{OPT}^{FIFO}\ge h\mathbb E[(\underline S-D)^+]+\theta\,\mathbb E[O_\infty(\underline S)].\quad(18)$$
--
--   This lower bound on the optimal cost is what makes the bounded-demand estimate (26) possible.
--
--   **Formalization Note** The inequality is in $[0,\infty]$. $\mathbb E[O_\infty(S)]$ is the limsup of the Cesàro averages of $\mathbb E[o^{\pi_S}_t]$ from the empty state, which is the paper's $\mathbb E[O_\infty(S)]$ by Lemma 1 (posed in mission 1 of this series).
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 22, Proposition 3, (18)

import Definitions.Def_PerishBaseStock_Penalty_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishBaseStock.Penalty

/-- Proposition 3 (18): with bounded demand,
`OPT ≥ h E[(S̲ - D)^+] + θ E[O∞(S̲)]`. -/
theorem proposition_3 (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (hP : DemandBounded P) :
    ENNReal.ofReal (c.h * LostSalesOrderUpTo.Asymptotic.expectedHolding P.law (floorLevel c P)) +
        ENNReal.ofReal c.θ * avgOutdating c P (floorLevel c P) ≤ OPT c P := by sorry

end PerishBaseStock.Penalty
