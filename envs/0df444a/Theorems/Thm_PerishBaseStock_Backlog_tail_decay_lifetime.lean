-- Prove2me | Theorems.Thm_PerishBaseStock_Backlog_tail_decay_lifetime
-- name    : PerishBaseStock.Backlog.tail_decay_lifetime
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-22T19:31:15.164201+00:00
-- url     : https://prove2.me/theorems/a0b744c7-bbbd-4390-8cd4-758c8b350667
-- title:
--   Theorem 7(a), proof step — $E[(\widetilde S^L_m-\sum_{i=1}^{m+L}D_i)^+]$ decays exponentially in $m$
-- statement:
--   Consider the perishable backlogging system with lead time $L$, holding cost $h>0$, backlogging cost $b>0$ and outdating cost $\theta\ge hL$, with a fixed demand law ($D\ge0$, $0<E[D]<\infty$). For a lifetime $m\ge1$ let $\widetilde S^L_m$ be any minimizer over $[0,\infty)$ of
--   $$\widetilde C^L_m(S)=hE\Big[\Big(S-\sum_{i=1}^{L+1}D_i\Big)^+\Big]+bE\Big[\Big(\sum_{i=1}^{L+1}D_i-S\Big)^+\Big]+\frac{\theta-hL}{m+L}E\Big[\Big(S-\sum_{i=1}^{m+L}D_i\Big)^+\Big].$$
--   Then there are constants $K_1,K_2>0$, independent of $m$, such that for every $m\ge1$ and every such minimizer
--   $$E\Big[\Big(\widetilde S^L_m-\sum_{i=1}^{m+L}D_i\Big)^+\Big]\le K_1e^{-K_2m}.$$
--
--   This is the analytic step behind Theorem 7(a): combined with the gap bound (28) (whose coefficient is bounded in $m$), it yields exponential decay of the optimality gap in $m$. As in the proof of Theorem 1, it follows from a uniform bound on $\widetilde S^L_m$ and the Chernoff-type estimate $x^+\le e^{\lambda x}/(\lambda e)$ with $E[e^{-\lambda D}]<1$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, Management Science 69(2) 2023 (accepted manuscript https://ira.lib.polyu.edu.hk/bitstream/10397/94980/1/Bu_Asymptotic_Optimality_Base-Stock.pdf), p. 24, Sketched Proof of Theorem 7 (part (a) "follows similar arguments to those for Theorem 1"), via inequality (22) of the Theorem 1 proof, p. 23

import Definitions.Def_PerishBaseStock_Backlog_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PerishBaseStock.Backlog

open LostSalesOrderUpTo.Asymptotic in
/-- Theorem 7(a), proof step (analogue of (22), p. 24): with the demand law, `L`, `h`, `b`, `θ`
fixed, `E[(S̃^L_m - Σ_{i=1}^{m+L} D_i)^+]` decays exponentially in the lifetime `m`, uniformly
over the minimizers `S̃^L_m` of `C̃^L_m`. -/
theorem tail_decay_lifetime (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ K₂ : ℝ, 0 < K₂ ∧
      ∀ m : ℕ, 1 ≤ m → ∀ S : ℝ≥0, IsHeuristicLevel P { c with m := m } S →
        expectedHolding (leadTimeLaw P (m + c.L - 1)) S ≤ K₁ * Real.exp (-(K₂ * m)) := by sorry

end PerishBaseStock.Backlog
