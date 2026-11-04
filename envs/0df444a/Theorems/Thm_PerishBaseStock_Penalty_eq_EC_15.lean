-- Prove2me | Theorems.Thm_PerishBaseStock_Penalty_eq_EC_15
-- name    : PerishBaseStock.Penalty.eq_EC_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:28.405813+00:00
-- url     : https://prove2.me/theorems/0204d34f-c4fd-4057-a05a-4fec25984a5c
-- title:
--   (EC.15): $\mathbb E[O_\infty(S_2)]\le\mathbb E[O_\infty(S_1)]+S_2-S_1$ for $0\le S_1\le S_2$
-- statement:
--   Consider the lost-sales perishable inventory system with lifetime $m\ge1$, zero lead time and FIFO issuance, started empty, with i.i.d. demands. For a base-stock level $S\ge0$ let $\mathbb E[O_\infty(S)]$ be the long-run average outdated quantity under the base-stock policy $\pi_S$. Then for any $0\le S_1\le S_2$,
--
--   $$\mathbb E[O_\infty(S_2)]\le\mathbb E[O_\infty(S_1)]+S_2-S_1.$$
--
--   Raising the base-stock level by $\Delta$ raises the long-run average outdating by at most $\Delta$. No boundedness of demand is needed. The inequality is used in the second step of the proof of (26).
--
--   **Formalization Note** The inequality is in $[0,\infty]$, with $\mathbb E[O_\infty(S)]$ the limsup Cesàro average of $\mathbb E[o^{\pi_S}_t]$ from the empty state.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec6, Appendix B.2, inequality (EC.15)

import Definitions.Def_PerishBaseStock_Penalty_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishBaseStock.Penalty

/-- Inequality (EC.15): for `0 ≤ S₁ ≤ S₂`, `E[O∞(S₂)] ≤ E[O∞(S₁)] + S₂ - S₁`. -/
theorem eq_EC_15 (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (S₁ S₂ : ℝ≥0) (h12 : S₁ ≤ S₂) :
    avgOutdating c P S₂ ≤ avgOutdating c P S₁ + ENNReal.ofReal ((S₂ : ℝ) - S₁) := by sorry

end PerishBaseStock.Penalty
