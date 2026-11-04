-- Prove2me | Theorems.Thm_PerishBaseStock_Lifetime_eq_19_outdating_recursion
-- name    : PerishBaseStock.Lifetime.eq_19_outdating_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:52.772987+00:00
-- url     : https://prove2.me/theorems/749e680d-98c3-435e-9b59-69fa506ed8c5
-- title:
--   (19) — the FIFO outdating recursion $o^\pi_{t+m-1}=(x^\pi_{t,m}-\sum D_i-\sum o^\pi_j)^+$
-- statement:
--   Consider the perishable inventory system with lifetime $m\ge 1$ and FIFO issuance, started empty, and let $\pi$ be any admissible policy. Write $x^\pi_{t,m}$ for the total inventory level after ordering in period $t$ and $o^\pi_t$ for the amount outdated in period $t$. Then for every demand sample path and every period $t\ge 1$,
--   $$o^\pi_{t+m-1}=\Big(x^\pi_{t,m}-\sum_{i=t}^{t+m-1}D_i-\sum_{j=t}^{t+m-2}o^\pi_j\Big)^+ .$$
--
--   In words: the stock on hand in period $t$ all perishes by period $t+m-1$; under FIFO it is consumed first by the demands of periods $t,\dots,t+m-1$, and what is not consumed or already outdated in periods $t,\dots,t+m-2$ outdates in period $t+m-1$. This recursion underlies the comparison of outdating processes in the proofs of Lemma 1 and of the later theorems of the series.
--
--   **Formalization Note** Time is zero-based (Lean period $t$ is the paper's $t+1$), so the sums run over `Finset.Ico t (t + m)` and `Finset.Ico t (t + m - 1)`. The printed inner sum $\sum_{j=t}^{t+m-2}o^\pi_i$ is read as $\sum_j o^\pi_j$ (a typographical slip in the source).
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 22, display (19)

import Definitions.Def_PerishBaseStock_Lifetime_Model
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Lifetime

theorem eq_19_outdating_recursion {m : ℕ} (hm : 1 ≤ m) (π : Policy m)
    (d : CappedBaseStock.DemandPath) (t : ℕ) :
    outdated π d (t + m - 1) =
      max (upTo π d t - ∑ i ∈ Finset.Ico t (t + m), (d i : ℝ) -
        ∑ j ∈ Finset.Ico t (t + m - 1), outdated π d j) 0 := by sorry

end PerishBaseStock.Lifetime
