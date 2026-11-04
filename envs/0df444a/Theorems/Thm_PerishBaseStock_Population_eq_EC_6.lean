-- Prove2me | Theorems.Thm_PerishBaseStock_Population_eq_EC_6
-- name    : PerishBaseStock.Population.eq_EC_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:51.104698+00:00
-- url     : https://prove2.me/theorems/31f99a9a-2263-4ac2-a302-0414b19cfa87
-- title:
--   (EC.6) — Scarf's bound $S^{NP}_n\le\mathbb E[D(n)]+\sqrt{p\,\mathrm{Var}[D(n)]/h}$
-- statement:
--   Let the generic one-period demand be $D(n)=\sum_{j=1}^{N(n)}\hat D_j$ of the population form (7), with $\mathbb E[\hat D_1]>0$, and let $h>0$, $p>0$. Let $S^{NP}_n=F_n^{-1}(p/(p+h))$ be the newsvendor level of $D(n)$, where $F_n$ is its distribution function and $F_n^{-1}(x)=\inf\{y:F_n(y)\ge x\}$. For every positive integer $n$,
--   $$
--   S^{NP}_n\le\mathbb E[D(n)]+\sqrt{\frac{p\,\mathrm{Var}[D(n)]}{h}} .
--   $$
--
--   The bound uses only the mean and the variance of $D(n)$; it controls the growth of $S^{NP}_n$ in $n$.
--
--   **Formalization Note** $\mathbb E[D(n)]$ and $\mathrm{Var}[D(n)]$ are the mean and the variance of the law $P_n$ of $D(n)$. Under (7) the variance is finite.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec3, App. B.1, (EC.6)

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Population

/-- **(EC.6)** (Bu, Gong & Chao, App. B.1, p. ec3). With demand of form (7), for every positive
integer `n`, `S^NP_n ≤ E[D(n)] + √(p Var[D(n)] / h)`. -/
theorem eq_EC_6 (c : PerishBaseStock.Lifetime.Params) (Dh : CustomerLaw) (X : InterarrivalLaw)
    (hμ : 0 < customerMean Dh)
    (P : ℕ → CappedBaseStock.DemandLaw) (hP : IsPopulationFamily Dh X P)
    (n : ℕ) (hn : 1 ≤ n) :
    (newsvendorLevel (P n) c : ℝ) ≤
      CappedBaseStock.mean (P n) +
        Real.sqrt (c.p * variance (fun x : ℝ≥0 => (x : ℝ)) (P n).law / c.h) := by sorry

end PerishBaseStock.Population
