-- Prove2me | Theorems.Thm_PerishBaseStock_Outdating_theorem_4
-- name    : PerishBaseStock.Outdating.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:37.934565+00:00
-- url     : https://prove2.me/theorems/27aee539-5c88-4cc3-9c80-cb554a3008b1
-- title:
--   Theorem 4 — $\lim_{\theta\to\infty}(C_\theta(\widetilde S_\theta)-\mathrm{OPT}_\theta)=0$ under FIFO issuance
-- statement:
--   Consider the FIFO lost-sales perishable inventory system with lifetime $m\ge1$, i.i.d. non-negative demands with $0<\mathbb E[D]<\infty$, holding cost $h>0$, penalty cost $p>0$ and outdating cost $\theta\ge0$, starting empty. For each $\theta\ge0$ let $\widetilde S_\theta$ be a minimizer over $[0,\infty)$ of
--   $$\widetilde C_\theta(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\frac{\theta}{m}\mathbb E\Big[\Big(S-\sum_{i=1}^m D_i\Big)^+\Big],$$
--   let $C_\theta(S)$ be the long-run average cost of the base-stock policy $\pi_S$, and let $\mathrm{OPT}_\theta$ be the optimal long-run average cost over all admissible policies. Then $C_\theta(\widetilde S_\theta)<\infty$ for every $\theta$, and
--   $$\lim_{\theta\to\infty}\big(C_\theta(\widetilde S_\theta)-\mathrm{OPT}_\theta\big)=0.$$
--
--   The heuristic base-stock policy is therefore asymptotically optimal when outdating is expensive, with $h$, $p$, $m$ and the demand law held fixed. No condition on the lower support of demand is needed.
--
--   **Formalization Note** The statement holds for every selection $\theta\mapsto\widetilde S_\theta$ of minimizers. Costs are in $[0,\infty]$; the difference is taken between real values (`toReal`), and the finiteness of $C_\theta(\widetilde S_\theta)$ is part of the conclusion, which also makes $\mathrm{OPT}_\theta\le C_\theta(\widetilde S_\theta)$ finite, so no $\infty-\infty$ convention enters. $\theta$ ranges over $\mathbb R_{\ge0}$ and the limit is along `atTop` there, which is the paper's $\theta\to\infty$ over $\theta\ge0$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 14, Theorem 4

import Definitions.Def_PerishBaseStock_Outdating_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PerishBaseStock.Outdating

theorem theorem_4 (P : CappedBaseStock.DemandLaw) (c : Params) (St : ℝ≥0 → ℝ≥0)
    (hSt : ∀ θ : ℝ≥0, IsHeurMin P c θ (St θ)) :
    (∀ θ : ℝ≥0, bsCost P c θ (St θ) < ⊤) ∧
      Tendsto (fun θ : ℝ≥0 => (bsCost P c θ (St θ)).toReal - (OPT P c θ).toReal)
        atTop (𝓝 0) := by sorry

end PerishBaseStock.Outdating
