-- Prove2me | Theorems.Thm_PerishBaseStock_Backlog_ec_30
-- name    : PerishBaseStock.Backlog.ec_30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:23.301738+00:00
-- url     : https://prove2.me/theorems/27edc669-176c-435a-b7eb-892164d72e8d
-- title:
--   (EC.30) Outdating over m + L periods dominates the excess of the inventory position over demand
-- statement:
--   Consider the perishable backlogging system with lifetime $m\ge1$ and lead time $L\ge0$ under FIFO issuance. For every admissible policy $\pi$, every demand sample path and every period $t\ge1$,
--
--   $$\sum_{i=t}^{t+m+L-1}o^\pi_i\ \ge\ \Big(x^\pi_{t,m+L}-\sum_{i=t}^{t+m+L-1}D_i\Big)^+ .$$
--
--   Every unit in the inventory position of period $t$ is either consumed by the demands of periods $t,\dots,t+m+L-1$ or outdates by period $t+m+L-1$; the inequality is the sample-path lower bound on outdating used for (14) and Proposition 4.
--
--   **Formalization Note** Pathwise statement with zero-based time; the sums run over the $m+L$ Lean periods $t,\dots,t+m+L-1$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec11, (EC.30)

import Definitions.Def_PerishBaseStock_Backlog_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Backlog

/-- (EC.30), p. ec11: for any admissible policy and any demand path,
`Σ_{i=t}^{t+m+L-1} o^π_i ≥ (x^π_{t,m+L} - Σ_{i=t}^{t+m+L-1} D_i)^+` (zero-based `t`). -/
theorem ec_30 (c : Params) (hm : 1 ≤ c.m) (π : Policy c) (d : CappedBaseStock.DemandPath)
    (t : ℕ) :
    max (levelAt c π d t (c.m + c.L) - ∑ i ∈ Finset.Ico t (t + c.m + c.L), (d i : ℝ)) 0 ≤
      ∑ i ∈ Finset.Ico t (t + c.m + c.L), outdatedAt c π d i := by sorry

end PerishBaseStock.Backlog
