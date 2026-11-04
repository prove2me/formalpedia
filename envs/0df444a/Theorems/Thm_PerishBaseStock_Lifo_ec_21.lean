-- Prove2me | Theorems.Thm_PerishBaseStock_Lifo_ec_21
-- name    : PerishBaseStock.Lifo.ec_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:16.412228+00:00
-- url     : https://prove2.me/theorems/1c12f2a3-521b-42a4-9da1-03da4d48e773
-- title:
--   (EC.21) — $\lim_\theta\mathrm{OPT}^{LIFO}_\theta\ge\lim_\theta\widetilde C_\theta(\widetilde S_\theta)=\min_{0\le S\le m\underline D}\{hE[(S-D)^+]+pE[(D-S)^+]\}$
-- statement:
--   Fix the lifetime $m\ge 1$ and the costs $h>0$, $p>0$, and let the outdating cost $\theta$ vary. For each $\theta\ge 0$ let $\widetilde S_\theta$ be any minimizer of $\widetilde C_\theta$ over $[0,\infty)$, and let $\underline D$ be the lower support of demand. Then $\widetilde C_\theta(\widetilde S_\theta)$ converges as $\theta\to\infty$, the optimal LIFO cost $\mathrm{OPT}^{LIFO}_\theta$ converges in $[0,\infty]$, and
--   $$\lim_{\theta\to\infty}\mathrm{OPT}^{LIFO}_\theta\ \ge\ \lim_{\theta\to\infty}\widetilde C_\theta(\widetilde S_\theta)=\min_{0\le S\le m\underline D}\big\{h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]\big\}.$$
--
--   This is the lower half of the proof of Theorem 5(c): with $\underline D=0$ the right side is $p\mathbb E[D]$.
--
--   **Formalization Note** The existence of both limits is part of the conclusion (the paper writes $\lim$). The minimum over $[0,m\underline D]$ is written as an infimum over that interval, which has the same value because the function is continuous on a compact interval. The conclusion holds for every selection $\theta\mapsto\widetilde S_\theta$ of minimizers; $\theta$ is varied by record update of the parameters.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec8, Appendix C.2, (EC.21)

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.Lifo

/-- (EC.21): as `θ → ∞`, `C̃_θ(S̃_θ)` converges to `min_{0 ≤ S ≤ mD̲} {hE[(S-D)⁺] + pE[(D-S)⁺]}`,
and `OPT^{LIFO}_θ` converges to a limit at least as large, for every selection of minimizers. -/
theorem ec_21 (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (St : ℝ → ℝ≥0) (hSt : ∀ θ : ℝ, 0 ≤ θ → IsTildeMinimizer P { c with θ := θ } (St θ)) :
    Tendsto (fun θ : ℝ => tildeC P { c with θ := θ } (St θ)) atTop
        (𝓝 (⨅ S : {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)},
          backorderCost P.law c.h c.p S.val)) ∧
      ∃ L : ℝ≥0∞, Tendsto (fun θ : ℝ => OPT P { c with θ := θ }) atTop (𝓝 L) ∧
        ENNReal.ofReal (⨅ S : {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)},
          backorderCost P.law c.h c.p S.val) ≤ L := by sorry

end PerishBaseStock.Lifo
