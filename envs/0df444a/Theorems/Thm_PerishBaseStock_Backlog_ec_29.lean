-- Prove2me | Theorems.Thm_PerishBaseStock_Backlog_ec_29
-- name    : PerishBaseStock.Backlog.ec_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:22.272026+00:00
-- url     : https://prove2.me/theorems/cb70b516-e16b-4f66-b924-f4daaa8671b0
-- title:
--   (EC.29) Net inventory after the lead time equals the inventory position minus demand and outdating
-- statement:
--   Consider the perishable backlogging system with lifetime $m\ge1$ and lead time $L\ge0$ under FIFO issuance. For every admissible policy $\pi$, every demand sample path and every period $t\ge1$,
--
--   $$x^\pi_{t+L,m}=x^\pi_{t,m+L}-\sum_{i=t}^{t+L-1}D_i-\sum_{i=t}^{t+L-1}o^\pi_i ,$$
--
--   where $x^\pi_{t,m+L}$ is the inventory position after ordering in period $t$, $x^\pi_{t+L,m}$ the net on-hand inventory of period $t+L$, and $o^\pi_i$ the outdated quantity of period $i$.
--
--   The identity is the lead-time bookkeeping used in the proof of the lower bound (14) of Lemma 5 and of Proposition 4.
--
--   **Formalization Note** Pathwise statement with zero-based time ($t$ in Lean is the paper's $t+1$); the sums run over Lean periods $t,\dots,t+L-1$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec11, (EC.29)

import Definitions.Def_PerishBaseStock_Backlog_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Backlog

/-- (EC.29), p. ec11: for any admissible policy and any demand path,
`x^π_{t+L,m} = x^π_{t,m+L} - Σ_{i=t}^{t+L-1} D_i - Σ_{i=t}^{t+L-1} o^π_i` (zero-based `t`). -/
theorem ec_29 (c : Params) (hm : 1 ≤ c.m) (π : Policy c) (d : CappedBaseStock.DemandPath)
    (t : ℕ) :
    levelAt c π d (t + c.L) c.m =
      levelAt c π d t (c.m + c.L) - ∑ i ∈ Finset.Ico t (t + c.L), (d i : ℝ) -
        ∑ i ∈ Finset.Ico t (t + c.L), outdatedAt c π d i := by sorry

end PerishBaseStock.Backlog
