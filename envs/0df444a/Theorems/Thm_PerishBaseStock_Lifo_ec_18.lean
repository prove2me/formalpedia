-- Prove2me | Theorems.Thm_PerishBaseStock_Lifo_ec_18
-- name    : PerishBaseStock.Lifo.ec_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:04.962526+00:00
-- url     : https://prove2.me/theorems/f4171db3-8726-427a-8c72-30ea7c8fcb68
-- title:
--   (EC.18) — the LIFO outdating recursion under $\pi_S$
-- statement:
--   Consider the LIFO perishable inventory system with lifetime $m\ge 1$, started empty, and run the base-stock policy $\pi_S$ with level $S\ge 0$. Write $o_t=o^{\pi_S}_t$ for the amount outdated in period $t$. Then, on every demand sample path $D_1,D_2,\dots$,
--   $$o_{t+m-1}=\min_{i\in\{0,\dots,m-1\}}\Big\{(S-D_{t+i})^+-\sum_{j=t+i}^{t+m-2}o_j\Big\}\qquad\text{for all }t\ge 1,$$
--   where an empty sum is $0$.
--
--   The recursion expresses the outdating in a period through the demands of the preceding $m$ periods and the outdating already incurred. It yields the lower bound (EC.19) on the outdating of $\pi_S$ and with it the lower half of Lemma 3.
--
--   **Formalization Note** Time is zero-based, so the Lean `t : ℕ` ranges over the paper's $t\ge 1$, and the sum is over `Finset.Ico (t + i) (t + m - 1)`. The statement depends only on $m$ and $S$, so the cost parameters do not appear.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec7, Appendix C.1, (EC.18)

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.Lifo

/-- (EC.18): the LIFO outdating recursion under `π_S`, on every demand path. Lean period
`t` is the paper's `t + 1`, so `∀ t : ℕ` is the paper's `∀ t ≥ 1`. -/
theorem ec_18 (m : ℕ) (hm : 1 ≤ m) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    outdated (baseStock m S) d (t + m - 1) =
      (Finset.range m).inf' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun i => max ((S : ℝ) - d (t + i)) 0 -
          ∑ j ∈ Finset.Ico (t + i) (t + m - 1), outdated (baseStock m S) d j) := by sorry

end PerishBaseStock.Lifo
