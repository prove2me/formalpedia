-- Prove2me | Theorems.Thm_PerishBaseStock_Penalty_eq_26
-- name    : PerishBaseStock.Penalty.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:30.926901+00:00
-- url     : https://prove2.me/theorems/cbb8500d-2ca5-4792-87cc-cc8827478522
-- title:
--   (26): with bounded demand, $C(\widetilde S)-\mathrm{OPT}\le(h+\theta)(\bar D-\underline S)$
-- statement:
--   Consider the lost-sales perishable inventory system with lifetime $m\ge1$, zero lead time and FIFO issuance, with costs $h>0$, $p>0$, $\theta\ge0$ and i.i.d. demands with $0<\mathbb E[D]<\infty$. Suppose demand is bounded, $\bar D=\sup\{x:F(x)<1\}<\infty$. Let $\widetilde S$ be any minimizer over $[0,\infty)$ of the heuristic cost $\widetilde C$ of (4), and let $\underline S$ be the least minimizer over $S\ge0$ of $h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\theta S$. Then
--
--   $$C(\widetilde S)-\mathrm{OPT}\le(h+\theta)(\bar D-\underline S).$$
--
--   This is the bounded-demand half of the proof of Theorem 3: as $p\to\infty$, $\underline S\to\bar D$ and the bound vanishes.
--
--   **Formalization Note** The gap is stated as $C(\widetilde S)\le\mathrm{OPT}+(h+\theta)(\bar D-\underline S)$ in $[0,\infty]$, equivalent to the printed difference because $\mathrm{OPT}<\infty$. $\underline S$ is evaluated at the current parameters.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 24, inequality (26); proof in Appendix B.2, p. ec6

import Definitions.Def_PerishBaseStock_Penalty_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishBaseStock.Penalty

/-- Inequality (26): with bounded demand, `C(S̃) - OPT ≤ (h + θ)(D̄ - S̲)` for every
minimizer `S̃` of `C̃`. -/
theorem eq_26 (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw)
    (hP : DemandBounded P) (S : ℝ≥0) (hS : IsHeuristicLevel c P S) :
    baseStockCost c P S ≤
      OPT c P + ENNReal.ofReal ((c.h + c.θ) * ((upperSupport P).toReal - floorLevel c P)) := by sorry

end PerishBaseStock.Penalty
