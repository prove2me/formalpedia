-- Prove2me | Theorems.Thm_PerishBaseStock_Lifo_hat_S_theta_limits
-- name    : PerishBaseStock.Lifo.hat_S_theta_limits
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:17.717271+00:00
-- url     : https://prove2.me/theorems/9ef4eaf9-e5fa-4a64-be6c-79622e4c2e69
-- title:
--   Proof of Theorem 5(c), p. ec8 — $\hat S_\theta\to\underline D$ and $\theta(E[(\hat S_\theta-D)^+]+E[(\hat S_\theta-\max\{D_1,\dots,D_m\})^+])\to0$
-- statement:
--   Fix the lifetime $m\ge 1$ and the costs $h>0$, $p>0$, and let the outdating cost $\theta$ vary. For each $\theta\ge 0$ let $\hat S_\theta$ be any minimizer of $(\hat C_{L,\theta}+\hat C_{U,\theta})/2$ over $[0,\infty)$, and let $\underline D=\inf\{x:F(x)>0\}$. Then
--   $$\lim_{\theta\to\infty}\hat S_\theta=\underline D\qquad\text{and}\qquad\lim_{\theta\to\infty}\theta\Big(\mathbb E[(\hat S_\theta-D)^+]+\mathbb E[(\hat S_\theta-\max\{D_1,\dots,D_m\})^+]\Big)=0.$$
--
--   As the outdating cost grows, the heuristic level is pushed down to the smallest possible demand, while the outdating cost it incurs still vanishes.
--
--   **Formalization Note** The conclusion is stated for every selection $\theta\mapsto\hat S_\theta$ of minimizers.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec8, Appendix C.2, display after (EC.21)

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.Lifo

/-- Proof of Theorem 5(c), p. ec8: `Ŝ_θ → D̲` and
`θ(E[(Ŝ_θ - D)⁺] + E[(Ŝ_θ - max{D_1,…,D_m})⁺]) → 0` as `θ → ∞`, for every selection of minimizers. -/
theorem hat_S_theta_limits (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (Sh : ℝ → ℝ≥0) (hSh : ∀ θ : ℝ, 0 ≤ θ → IsHatMinimizer P { c with θ := θ } (Sh θ)) :
    Tendsto (fun θ : ℝ => (Sh θ : ℝ)) atTop (𝓝 (lowerSupport P : ℝ)) ∧
      Tendsto (fun θ : ℝ => θ * (expectedHolding P.law (Sh θ)
          + expectedHolding (maxLaw P (c.m - 1)) (Sh θ))) atTop (𝓝 0) := by sorry

end PerishBaseStock.Lifo
