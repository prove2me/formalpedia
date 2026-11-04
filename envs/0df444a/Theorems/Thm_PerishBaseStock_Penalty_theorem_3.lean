-- Prove2me | Theorems.Thm_PerishBaseStock_Penalty_theorem_3
-- name    : PerishBaseStock.Penalty.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:44.0553+00:00
-- url     : https://prove2.me/theorems/1af40417-33c4-4d3d-8adf-9b9429012d31
-- title:
--   Theorem 3: $\lim_{p\to\infty}(C_p(\widetilde S_p)-\mathrm{OPT}_p)=0$ under FIFO issuance
-- statement:
--   Consider the periodic-review lost-sales inventory system of a perishable product with fixed lifetime $m\ge1$, zero lead time and FIFO issuance, started empty. Demands are i.i.d. copies of a non-negative random variable $D$ with $0<\mathbb E[D]<\infty$; the unit holding cost $h>0$ and the unit outdating cost $\theta\ge0$ are fixed, and the unit lost-sales penalty $p>0$ varies. For each $p$ let $C_p(S)$ be the long-run average cost of the base-stock policy $\pi_S$, let $\mathrm{OPT}_p$ be the optimal long-run average cost over all admissible policies, and let $\widetilde S_p$ be any minimizer over $[0,\infty)$ of
--
--   $$\widetilde C_p(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\frac{\theta}{m}\mathbb E\Big[\Big(S-\sum_{i=1}^m D_i\Big)^+\Big].$$
--
--   Then
--
--   $$\lim_{p\to\infty}\big(C_p(\widetilde S_p)-\mathrm{OPT}_p\big)=0.$$
--
--   No boundedness assumption on demand is made: the theorem covers bounded and unbounded demand. It says that the explicitly computable heuristic base-stock policy is asymptotically optimal in the high-service-level regime where shortages are much more expensive than holding.
--
--   **Formalization Note** The statement quantifies over every selection $p\mapsto\widetilde S_p$ with $\widetilde S_p$ a minimizer of $\widetilde C_p$ for each $p>0$. Costs live in $[0,\infty]$; the difference is taken between real values (`toReal`), which is faithful because $C_p(S)\le hS+p\mathbb E[D]+\theta S<\infty$ and $\mathrm{OPT}_p\le C_p(\widetilde S_p)$. Only the field $p$ of the parameter record varies; $m$, $h$, $\theta$ and the demand law stay fixed and general.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 13, Theorem 3; proof sketch p. 24, proof in Appendix B.2, p. ec6

import Definitions.Def_PerishBaseStock_Penalty_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace PerishBaseStock.Penalty

/-- Theorem 3: with `m`, `h`, `θ` and the demand law fixed, the optimality gap of the
heuristic base-stock policy vanishes as the unit penalty cost `p` grows, for every selection
`p ↦ S̃_p` of minimizers of `C̃_p`. -/
theorem theorem_3 (c : Params) (hm : 1 ≤ c.m) (hh : 0 < c.h) (hθ : 0 ≤ c.θ)
    (P : CappedBaseStock.DemandLaw) (S : ℝ → ℝ≥0)
    (hS : ∀ p : ℝ, 0 < p → IsHeuristicLevel { c with p := p } P (S p)) :
    Tendsto (fun p : ℝ => (baseStockCost { c with p := p } P (S p)).toReal -
      (OPT { c with p := p } P).toReal) atTop (𝓝 0) := by sorry

end PerishBaseStock.Penalty
