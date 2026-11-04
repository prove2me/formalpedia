-- Prove2me | Theorems.Thm_PerishBaseStock_Lifetime_eq_21_gap_bound
-- name    : PerishBaseStock.Lifetime.eq_21_gap_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:48.744297+00:00
-- url     : https://prove2.me/theorems/02656b9d-7315-4b3b-b575-a7758083d670
-- title:
--   (21) — $C(\widetilde S)-\mathrm{OPT}\le\frac{(m-1)\theta}{m}\mathbb E[(\widetilde S-\sum_{i\le m}D_i)^+]$
-- statement:
--   Consider the perishable lost-sales inventory system with lifetime $m\ge 1$ and FIFO issuance, with costs $h>0$, $p>0$, $\theta\ge 0$, and let $\widetilde S$ be any minimizer of the heuristic cost $\widetilde C$ over $[0,+\infty)$. Then the long-run average cost of the base-stock policy $\pi_{\widetilde S}$ satisfies
--   $$C(\widetilde S)-\mathrm{OPT}\;\le\;\frac{(m-1)\theta}{m}\,\mathbb E\Big[\Big(\widetilde S-\sum_{i=1}^m D_i\Big)^+\Big].$$
--
--   This optimality-gap bound is the common starting point of the proofs of Theorems 1, 2 and 4 of the paper.
--
--   **Formalization Note** The gap is stated as $C(\widetilde S)\le\mathrm{OPT}+B$ in $[0,\infty]$, which avoids truncated subtraction; this is equivalent to the paper's inequality because $\mathrm{OPT}\le C(0)=p\,\mathbb E[D]<\infty$. $m-1$ is computed in $\mathbb R$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 23, display (21)

import Definitions.Def_PerishBaseStock_Lifetime_Model
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Lifetime

theorem eq_21_gap_bound (P : CappedBaseStock.DemandLaw) (c : Params) (Stilde : ℝ≥0)
    (hS : IsHeuristicLevel P c Stilde) :
    bsCost P c Stilde ≤ OPT P c + ENNReal.ofReal (((c.m : ℝ) - 1) * c.θ / c.m *
      LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1)) Stilde) := by sorry

end PerishBaseStock.Lifetime
