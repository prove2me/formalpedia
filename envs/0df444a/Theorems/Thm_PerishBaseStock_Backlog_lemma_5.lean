-- Prove2me | Theorems.Thm_PerishBaseStock_Backlog_lemma_5
-- name    : PerishBaseStock.Backlog.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:23.133011+00:00
-- url     : https://prove2.me/theorems/b7e7f780-318b-4fc0-889a-a74189f2423d
-- title:
--   Lemma 5 — upper bound (13) and lower bound (14) on the cost $C^L(S)$ of a base-stock policy
-- statement:
--   Consider the perishable backlogging system with lifetime $m\ge1$, lead time $L\ge0$, costs $h,b>0$ and $\theta\ge hL$, under FIFO issuance, starting empty. For every base-stock level $S\ge0$ the long-run average cost $C^L(S)$ of the base-stock policy $\pi_S$ satisfies
--
--   $$C^L(S)\le h\mathbb E\Big[\Big(S-\sum_{i=1}^{L+1}D_i\Big)^+\Big]+b\mathbb E\Big[\Big(\sum_{i=1}^{L+1}D_i-S\Big)^+\Big]+(\theta+bL)\mathbb E\Big[\Big(S-\sum_{i=1}^{m+L}D_i\Big)^+\Big]\qquad(13)$$
--
--   and
--
--   $$C^L(S)\ge\widetilde C^L(S)=h\mathbb E\Big[\Big(S-\sum_{i=1}^{L+1}D_i\Big)^+\Big]+b\mathbb E\Big[\Big(\sum_{i=1}^{L+1}D_i-S\Big)^+\Big]+\frac{\theta-hL}{m+L}\mathbb E\Big[\Big(S-\sum_{i=1}^{m+L}D_i\Big)^+\Big].\qquad(14)$$
--
--   The two bounds sandwich the cost of every base-stock policy between explicit newsvendor-type functions; (14) at $\widetilde S^L$ is the lower bound on the optimal cost of Proposition 4.
--
--   **Formalization Note** $C^L(S)\in[0,\infty]$ and the right-hand sides are real numbers embedded with `ENNReal.ofReal` (they are nonnegative because $\theta\ge hL$). The paper states the lemma also for $L=0$; so does the Lean statement. At $m=1$, $L=0$ the state is empty and a backlog cannot be carried, but for base-stock policies the cost is unaffected.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 19, Lemma 5, (13)–(14)

import Definitions.Def_PerishBaseStock_Backlog_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Backlog

open LostSalesOrderUpTo.Asymptotic in
/-- Lemma 5, p. 19: for any `L ≥ 0` and `S ≥ 0`, the upper bound (13) and the lower
bound (14) `C^L(S) ≥ C̃^L(S)` on the long-run average cost of the base-stock policy. -/
theorem lemma_5 (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing) (S : ℝ≥0) :
    bsCost P c S ≤ ENNReal.ofReal
        (c.h * expectedHolding (leadTimeLaw P c.L) S +
          c.b * expectedShortfall (leadTimeLaw P c.L) S +
          (c.θ + c.b * c.L) * expectedHolding (leadTimeLaw P (c.m + c.L - 1)) S) ∧
      ENNReal.ofReal (heuristicCost P c S) ≤ bsCost P c S := by sorry

end PerishBaseStock.Backlog
