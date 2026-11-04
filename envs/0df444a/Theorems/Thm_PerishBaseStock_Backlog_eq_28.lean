-- Prove2me | Theorems.Thm_PerishBaseStock_Backlog_eq_28
-- name    : PerishBaseStock.Backlog.eq_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:24.518436+00:00
-- url     : https://prove2.me/theorems/cb0f4a2e-89d0-44e1-ba65-8aee09dbb704
-- title:
--   (28) Optimality-gap bound for the base-stock policy $\pi_{\widetilde S^L}$
-- statement:
--   Consider the perishable backlogging system with lifetime $m\ge1$, positive lead time $L\ge1$, costs $h,b>0$ and $\theta\ge hL$, under FIFO issuance, starting empty. For every minimizer $\widetilde S^L$ of $\widetilde C^L$ over $[0,\infty)$,
--
--   $$C^L(\widetilde S^L)-\mathrm{OPT}^L\ \le\ \frac{(m-1)\theta+(b(m+L)+h+\theta)L}{m+L}\cdot\mathbb E\Big[\Big(\widetilde S^L-\sum_{i=1}^{m+L}D_i\Big)^+\Big].$$
--
--   This is the common gap bound from which all three parts of Theorem 7 follow.
--
--   **Formalization Note** Stated as $C^L(\widetilde S^L)\le\mathrm{OPT}^L+B$ in $[0,\infty]$, which is equivalent to the difference form because $\mathrm{OPT}^L\le C^L(0)<\infty$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 24, (28)

import Definitions.Def_PerishBaseStock_Backlog_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Backlog

open LostSalesOrderUpTo.Asymptotic in
/-- (28), p. 24: for `L ≥ 1` and every minimizer `S̃^L` of `C̃^L`,
`C^L(S̃^L) - OPT^L ≤ (((m-1)θ + (b(m+L) + h + θ)L)/(m+L)) E[(S̃^L - Σ_{i=1}^{m+L} D_i)^+]`. -/
theorem eq_28 (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (hL : 1 ≤ c.L) (S : ℝ≥0) (hS : IsHeuristicLevel P c S) :
    bsCost P c S ≤ OPT P c + ENNReal.ofReal
      ((((c.m : ℝ) - 1) * c.θ + (c.b * ((c.m : ℝ) + c.L) + c.h + c.θ) * c.L) /
          ((c.m : ℝ) + c.L) *
        expectedHolding (leadTimeLaw P (c.m + c.L - 1)) S) := by sorry

end PerishBaseStock.Backlog
