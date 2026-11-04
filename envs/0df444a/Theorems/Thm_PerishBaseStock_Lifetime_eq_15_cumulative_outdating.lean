-- Prove2me | Theorems.Thm_PerishBaseStock_Lifetime_eq_15_cumulative_outdating
-- name    : PerishBaseStock.Lifetime.eq_15_cumulative_outdating
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:49.442955+00:00
-- url     : https://prove2.me/theorems/4db98fa3-5603-44f8-bc7d-c27d25b20a52
-- title:
--   (15) — $\sum_{i=t}^{t+m-1}o^\pi_i\ge(x^\pi_{t,m}-\sum_{i=t}^{t+m-1}D_i)^+$
-- statement:
--   Consider the perishable inventory system with lifetime $m\ge 1$ and FIFO issuance, started empty, and let $\pi$ be any admissible policy. For every demand sample path and every period $t\ge 1$,
--   $$\sum_{i=t}^{t+m-1}o^\pi_i\;\ge\;\Big(x^\pi_{t,m}-\sum_{i=t}^{t+m-1}D_i\Big)^+ .$$
--
--   The total inventory $x^\pi_{t,m}$ of period $t$ either meets demand or outdates in periods $t,\dots,t+m-1$, and at most $\sum_{i=t}^{t+m-1}D_i$ of it can meet demand. Averaging this inequality over $t$ is the first step of the lower bound on the optimal cost (Proposition 2).
--
--   **Formalization Note** The paper states (15) under any issuance policy; only the FIFO system of §2 is formalized here. Time is zero-based (Lean period $t$ is the paper's $t+1$).
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 21, display (15)

import Definitions.Def_PerishBaseStock_Lifetime_Model
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Lifetime

theorem eq_15_cumulative_outdating {m : ℕ} (hm : 1 ≤ m) (π : Policy m)
    (d : CappedBaseStock.DemandPath) (t : ℕ) :
    max (upTo π d t - ∑ i ∈ Finset.Ico t (t + m), (d i : ℝ)) 0 ≤
      ∑ i ∈ Finset.Ico t (t + m), outdated π d i := by sorry

end PerishBaseStock.Lifetime
