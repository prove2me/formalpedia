-- Prove2me | Theorems.Thm_PerishBaseStock_Backlog_theta_tail_vanishes
-- name    : PerishBaseStock.Backlog.theta_tail_vanishes
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-22T19:31:21.71018+00:00
-- url     : https://prove2.me/theorems/d584fa7c-e87a-4a2a-90da-7e2aea19089a
-- title:
--   Theorem 7(c), proof step — $\theta\,E[(\widetilde S^L_\theta-\sum_{i=1}^{m+L}D_i)^+]\to0$ as $\theta\to\infty$
-- statement:
--   Consider the perishable backlogging system with lead time $L$, lifetime $m\ge1$, $h,b>0$ and a fixed demand law, and let the unit outdating cost $\theta\ge hL$ vary. For each $\theta\ge hL$ let $\widetilde S^L_\theta$ be any minimizer over $[0,\infty)$ of
--   $$\widetilde C^L_\theta(S)=hE\Big[\Big(S-\sum_{i=1}^{L+1}D_i\Big)^+\Big]+bE\Big[\Big(\sum_{i=1}^{L+1}D_i-S\Big)^+\Big]+\frac{\theta-hL}{m+L}E\Big[\Big(S-\sum_{i=1}^{m+L}D_i\Big)^+\Big].$$
--   Then
--   $$\lim_{\theta\to\infty}\theta\,E\Big[\Big(\widetilde S^L_\theta-\sum_{i=1}^{m+L}D_i\Big)^+\Big]=0.$$
--
--   This is the lead-time analogue of identity (24) and is the analytic step behind Theorem 7(c): the coefficient in the gap bound (28) grows linearly in $\theta$, so the gap vanishes once $\theta$ times the expected excess vanishes.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, Management Science 69(2) 2023 (accepted manuscript https://ira.lib.polyu.edu.hk/bitstream/10397/94980/1/Bu_Asymptotic_Optimality_Base-Stock.pdf), p. 24, Sketched Proof of Theorem 7 (part (c) "follows similar arguments to those for Theorem 4"); analogue of identity (24), p. 23, proved in Appendix B.3 (pp. ec6-ec7); $\widetilde S^L_\infty$ on p. 20

import Definitions.Def_PerishBaseStock_Backlog_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PerishBaseStock.Backlog

open LostSalesOrderUpTo.Asymptotic in
/-- Theorem 7(c), proof step (analogue of identity (24), p. 23, and Appendix B.3): for any
choice of minimizers `S̃^L_θ` of `C̃^L_θ`, `θ ≥ hL`, one has
`θ · E[(S̃^L_θ - Σ_{i=1}^{m+L} D_i)^+] → 0` as `θ → ∞`. -/
theorem theta_tail_vanishes (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (Sθ : ℝ → ℝ≥0)
    (hS : ∀ θ : ℝ, c.h * c.L ≤ θ → IsHeuristicLevel P { c with θ := θ } (Sθ θ)) :
    Tendsto (fun θ : ℝ => θ * expectedHolding (leadTimeLaw P (c.m + c.L - 1)) (Sθ θ))
      atTop (𝓝 0) := by sorry

end PerishBaseStock.Backlog
