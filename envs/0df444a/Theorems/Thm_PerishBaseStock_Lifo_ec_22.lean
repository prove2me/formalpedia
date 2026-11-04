-- Prove2me | Theorems.Thm_PerishBaseStock_Lifo_ec_22
-- name    : PerishBaseStock.Lifo.ec_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:15.139133+00:00
-- url     : https://prove2.me/theorems/99ffce29-95f2-495a-b740-fc5c5134163e
-- title:
--   (EC.22) — $\limsup_\theta C^{LIFO}_\theta(\hat S_\theta)\le p(E[D]-\underline D)$
-- statement:
--   Fix the lifetime $m\ge 1$ and the costs $h>0$, $p>0$, and let the outdating cost $\theta$ vary. For each $\theta\ge 0$ let $\hat S_\theta$ be any minimizer of $(\hat C_{L,\theta}+\hat C_{U,\theta})/2$ over $[0,\infty)$. Then the long-run average cost of the base-stock policy $\pi_{\hat S_\theta}$ in the LIFO system satisfies
--   $$\limsup_{\theta\to\infty}C^{LIFO}_\theta(\hat S_\theta)\le p\big(\mathbb E[D]-\underline D\big).$$
--
--   This is the upper half of the proof of Theorem 5(c), and the bound that mission 6 of this series combines with its own lower bound.
--
--   **Formalization Note** The paper's display (EC.22) also identifies $\limsup_\theta\hat C_{U,\theta}(\hat S_\theta)$ with $p(\mathbb E[D]-\underline D)$; only the outer inequality is formalized. The limsup is taken in $[0,\infty]$, for every selection $\theta\mapsto\hat S_\theta$ of minimizers.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec8, Appendix C.2, (EC.22)

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.Lifo

/-- (EC.22), outer inequality: `limsup_{θ→∞} C^{LIFO}_θ(Ŝ_θ) ≤ p(E[D] - D̲)`. -/
theorem ec_22 (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (Sh : ℝ → ℝ≥0) (hSh : ∀ θ : ℝ, 0 ≤ θ → IsHatMinimizer P { c with θ := θ } (Sh θ)) :
    Filter.limsup (fun θ : ℝ => baseStockCost P { c with θ := θ } (Sh θ)) atTop ≤
      ENNReal.ofReal (c.p * (CappedBaseStock.mean P - lowerSupport P)) := by sorry

end PerishBaseStock.Lifo
