-- Prove2me | Theorems.Thm_PerishBaseStock_Lifetime_lemma_2
-- name    : PerishBaseStock.Lifetime.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:55.005475+00:00
-- url     : https://prove2.me/theorems/79186836-bcb0-444b-85c1-1faa02b02209
-- title:
--   Lemma 2 — $\frac1m\mathbb E[(S-\sum_{i\le m} D_i)^+]\le\mathbb E[O_\infty(S)]\le\min\{\mathbb E[(S/m-D)^+],\mathbb E[(S-\sum_{i\le m} D_i)^+]\}$
-- statement:
--   Consider the perishable inventory system with lifetime $m\ge 1$ and FIFO issuance, and let $\bar o(S)$ be the long-run average expected outdating of the base-stock policy $\pi_S$ from the empty state (the paper's $\mathbb E[O_\infty(S)]$). For every $S\ge 0$,
--   $$\frac1m\,\mathbb E\Big[\Big(S-\sum_{i=1}^m D_i\Big)^+\Big]\;\le\;\bar o(S)\;\le\;\min\Big\{\mathbb E\Big[\Big(\frac Sm-D\Big)^+\Big],\ \mathbb E\Big[\Big(S-\sum_{i=1}^m D_i\Big)^+\Big]\Big\},$$
--   where $D_1,\dots,D_m$ are i.i.d. copies of the demand $D$.
--
--   The bounds go back to Chazan and Gal (1977, Theorem 2) and Cooper (2001, Proposition 3). The lower bound motivates the heuristic cost $\widetilde C$, and the upper bound by $\mathbb E[(S-\sum_{i\le m}D_i)^+]$ drives the exponential decay in the lifetime.
--
--   **Formalization Note** The three inequalities are stated separately in $[0,\infty]$, so the upper bounds also give finiteness of $\bar o(S)$. $\mathbb E[(S-\sum_{i\le m}D_i)^+]$ is `expectedHolding (leadTimeLaw P (m - 1)) S`.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 10, Lemma 2

import Definitions.Def_PerishBaseStock_Lifetime_Model
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Lifetime

theorem lemma_2 (P : CappedBaseStock.DemandLaw) (m : ℕ) (hm : 1 ≤ m) (S : ℝ≥0) :
    ENNReal.ofReal ((1 / (m : ℝ)) * LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (m - 1)) S) ≤ avgOutdate P m S ∧
      avgOutdate P m S ≤
        ENNReal.ofReal (LostSalesOrderUpTo.Asymptotic.expectedHolding P.law (S / (m : ℝ≥0))) ∧
      avgOutdate P m S ≤ ENNReal.ofReal (LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (m - 1)) S) := by sorry

end PerishBaseStock.Lifetime
