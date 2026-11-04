-- Prove2me | Theorems.Thm_PerishBaseStock_Penalty_eq_25
-- name    : PerishBaseStock.Penalty.eq_25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:55.415322+00:00
-- url     : https://prove2.me/theorems/60c59961-d1fa-4809-8194-84109ee16093
-- title:
--   (25): optimality gap of $\pi_{\widetilde S}$ is at most $\theta(\mathbb E[(D-\widetilde S/m)^+]-\mathbb E[(\frac1m\sum_{i=1}^m D_i-\widetilde S/m)^+])$
-- statement:
--   Consider the lost-sales perishable inventory system with lifetime $m\ge1$, zero lead time and FIFO issuance, with costs $h>0$, $p>0$, $\theta\ge0$ and i.i.d. demands $D,D_1,D_2,\dots$ with $0<\mathbb E[D]<\infty$. Let $\widetilde S$ be any minimizer over $[0,\infty)$ of the heuristic cost $\widetilde C$ of (4), let $C(\widetilde S)$ be the long-run average cost of the base-stock policy $\pi_{\widetilde S}$, and let $\mathrm{OPT}$ be the optimal long-run average cost over all admissible policies. Then
--
--   $$C(\widetilde S)-\mathrm{OPT}\le\theta\Big(\mathbb E\Big[\Big(D-\frac{\widetilde S}{m}\Big)^+\Big]-\mathbb E\Big[\Big(\frac1m\sum_{i=1}^m D_i-\frac{\widetilde S}{m}\Big)^+\Big]\Big).$$
--
--   The bound holds without any boundedness assumption on demand. It is the unbounded-demand half of the proof of Theorem 3: as $p\to\infty$ the minimizer $\widetilde S$ grows, and the right side is then shown to vanish.
--
--   **Formalization Note** The gap is stated as $C(\widetilde S)\le\mathrm{OPT}+B$ in $[0,\infty]$, with $B$ the right side (which is non-negative, since $\mathbb E[D]=\mathbb E[\frac1m\sum D_i]$). This is equivalent to the printed difference because $\mathrm{OPT}\le C(0)=p\mathbb E[D]<\infty$. Both expectations are Bochner integrals of integrable functions. $D_1,\dots,D_m$ are the first $m$ coordinates of the demand path.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 24, inequality (25)

import Definitions.Def_PerishBaseStock_Penalty_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishBaseStock.Penalty

/-- Inequality (25): the optimality gap of `π_S̃` is at most
`θ (E[(D - S̃/m)^+] - E[((1/m) Σ_{i=1}^m D_i - S̃/m)^+])`. -/
theorem eq_25 (c : Params) (hc : c.Standing) (P : CappedBaseStock.DemandLaw) (S : ℝ≥0)
    (hS : IsHeuristicLevel c P S) :
    baseStockCost c P S ≤ OPT c P + ENNReal.ofReal (c.θ *
      ((∫ x : ℝ≥0, max ((x : ℝ) - (S : ℝ) / (c.m : ℝ)) 0 ∂P.law) -
        ∫ d, max ((1 / (c.m : ℝ)) * (∑ i ∈ Finset.range c.m, (d i : ℝ)) - (S : ℝ) / (c.m : ℝ)) 0
          ∂CappedBaseStock.demandPathLaw P)) := by sorry

end PerishBaseStock.Penalty
