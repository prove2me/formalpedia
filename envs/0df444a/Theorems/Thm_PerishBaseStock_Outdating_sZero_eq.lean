-- Prove2me | Theorems.Thm_PerishBaseStock_Outdating_sZero_eq
-- name    : PerishBaseStock.Outdating.sZero_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:37.16965+00:00
-- url     : https://prove2.me/theorems/22cd5a18-596b-4e89-87dd-d7433bcb9ef0
-- title:
--   App. B.3, p. ec6 — $S^0=m\underline D$
-- statement:
--   Let $m\ge1$ and let $D_1,\dots,D_m$ be i.i.d. copies of the demand $D\ge0$, with lower support $\underline D=\inf\{x:F(x)>0\}$. Then
--   $$S^0:=\sup\Big\{S\ge 0:\mathbb E\Big[\Big(S-\sum_{i=1}^m D_i\Big)^+\Big]=0\Big\}=m\underline D.$$
--
--   In words, a base-stock level $S$ produces no stock surviving $m$ periods of demand exactly when $S\le m\underline D$. This identifies the threshold below which the heuristic level must eventually fall as $\theta\to\infty$.
--
--   **Formalization Note** The supremum is a real supremum of a set that is nonempty and bounded above, so it is the paper's value.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec6, App. B.3 ("One can verify that S⁰ = mD̲")

import Definitions.Def_PerishBaseStock_Outdating_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PerishBaseStock.Outdating

theorem sZero_eq (P : CappedBaseStock.DemandLaw) (c : Params) :
    sZero P c = (c.m : ℝ) * lowerSupport P := by sorry

end PerishBaseStock.Outdating
