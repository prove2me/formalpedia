-- Prove2me | Theorems.Thm_PerishBaseStock_Outdating_eq_24
-- name    : PerishBaseStock.Outdating.eq_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:36.646537+00:00
-- url     : https://prove2.me/theorems/e9abb172-bde8-49c6-8c91-6a82beadbe0a
-- title:
--   (24), p. 23 — $\lim_{\theta\to\infty}\theta\,\mathbb E[(\widetilde S_\theta-\sum_{i=1}^m D_i)^+]=0$
-- statement:
--   Let $m\ge1$, $h,p>0$, and let $\theta\mapsto\widetilde S_\theta$ be any selection of minimizers of the heuristic cost $\widetilde C_\theta$ of (4) over $[0,\infty)$, one for each $\theta\ge0$. Then
--   $$\lim_{\theta\to\infty}\theta\,\mathbb E\Big[\Big(\widetilde S_\theta-\sum_{i=1}^m D_i\Big)^+\Big]=0.\tag{24}$$
--
--   By inequality (21) (posed in mission 1 of this series), the optimality gap $C_\theta(\widetilde S_\theta)-\mathrm{OPT}_\theta$ is at most $\frac{(m-1)\theta}{m}\mathbb E[(\widetilde S_\theta-\sum_{i=1}^mD_i)^+]$, so (24) implies Theorem 4.
--
--   **Formalization Note** The selection is an arbitrary function $\mathbb R_{\ge0}\to\mathbb R_{\ge0}$ whose value at each $\theta$ is a minimizer; no monotonicity or measurability in $\theta$ is assumed. The expectation is a Bochner integral of the bounded function $(S-\sum D_i)^+$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 23, §6.2, (24)

import Definitions.Def_PerishBaseStock_Outdating_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PerishBaseStock.Outdating

theorem eq_24 (P : CappedBaseStock.DemandLaw) (c : Params) (St : ℝ≥0 → ℝ≥0)
    (hSt : ∀ θ : ℝ≥0, IsHeurMin P c θ (St θ)) :
    Tendsto (fun θ : ℝ≥0 => (θ : ℝ) * excessOverLifetimeDemand P c (St θ)) atTop (𝓝 0) := by sorry

end PerishBaseStock.Outdating
