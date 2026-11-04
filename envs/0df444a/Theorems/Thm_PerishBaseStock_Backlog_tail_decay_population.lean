-- Prove2me | Theorems.Thm_PerishBaseStock_Backlog_tail_decay_population
-- name    : PerishBaseStock.Backlog.tail_decay_population
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-22T19:31:33.39092+00:00
-- url     : https://prove2.me/theorems/482ee9f6-7657-4f47-8a30-b6184e4628fe
-- title:
--   Theorem 7(b), proof step — $E[(\widetilde S^L_n-\sum_{i=1}^{m+L}D_i(n))^+]$ decays exponentially in $n$
-- statement:
--   Consider the perishable backlogging system with lead time $L$, lifetime $m\ge2$, $h,b>0$ and $\theta\ge hL$, all fixed. Suppose that for every $n\ge1$ the one-period demand $D(n)$ has the form (7),
--   $$D(n)=\sum_{j=1}^{N(n)}\hat D_j,\qquad N(n)=\sup\Big\{N\in\mathbb N:\sum_{k=1}^N X_k/n\le1\Big\},$$
--   under the assumptions of Theorem 2 ($\hat D_j$ i.i.d. non-negative with finite mean and variance and $E[\hat D_1]>0$; $X_k$ i.i.d. non-negative with mean one, finite variance and $E[e^{sX_1}]<\infty$ for some $s>0$; the two families independent). Let $\widetilde S^L_n$ be any minimizer over $[0,\infty)$ of $\widetilde C^L$ computed under the demand law of $D(n)$. Then there are $K_1,K_2>0$ and $n_0$ such that for all $n\ge n_0$ and every such minimizer
--   $$E\Big[\Big(\widetilde S^L_n-\sum_{i=1}^{m+L}D_i(n)\Big)^+\Big]\le K_1e^{-K_2n},$$
--   where $D_1(n),D_2(n),\dots$ are i.i.d. copies of $D(n)$.
--
--   This is the analytic step behind Theorem 7(b): together with the gap bound (28), whose coefficient does not depend on $n$, it gives exponential decay of the optimality gap in the population size. The restriction $m\ge2$ matches the paper's argument (the gap between $\widetilde S^L_n\approx(L+1)nE[\hat D_1]$ and $\sum_{i=1}^{m+L}D_i(n)\approx(m+L)nE[\hat D_1]$ grows linearly in $n$ only when $m\ge2$).
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, Management Science 69(2) 2023 (accepted manuscript https://ira.lib.polyu.edu.hk/bitstream/10397/94980/1/Bu_Asymptotic_Optimality_Base-Stock.pdf), p. 24, Sketched Proof of Theorem 7 (part (b) "follows similar arguments to those for Theorem 2"); demand form (7) and assumptions of Theorem 2, pp. 11-12; proof of Theorem 2 via (23) p. 23 and Appendix B.1

import Definitions.Def_PerishBaseStock_Backlog_Model
import Definitions.Def_PerishBaseStock_Backlog_Population

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PerishBaseStock.Backlog

open LostSalesOrderUpTo.Asymptotic in
/-- Theorem 7(b), proof step (analogue of (23) and Appendix B.1): if the one-period demand has
the form (7) under the assumptions of Theorem 2 and the lifetime is `m ≥ 2`, then
`E[(S̃^L_n - Σ_{i=1}^{m+L} D_i(n))^+]` decays exponentially in the population size `n`,
uniformly over the minimizers `S̃^L_n` of `C̃^L_n`. -/
theorem tail_decay_population (c : Params) (hc : c.Standing) (hm : 2 ≤ c.m)
    (M : PopulationModel) (Pn : ℕ → CappedBaseStock.DemandLaw)
    (hPn : ∀ n : ℕ, 1 ≤ n → (Pn n).law = popDemandLaw M n) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ K₂ : ℝ, 0 < K₂ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ S : ℝ≥0, IsHeuristicLevel (Pn n) c S →
        expectedHolding (leadTimeLaw (Pn n) (c.m + c.L - 1)) S ≤
          K₁ * Real.exp (-(K₂ * n)) := by sorry

end PerishBaseStock.Backlog
