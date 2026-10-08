-- Prove2me | Theorems.Thm_TsayQF_NoCommit_proposition_1
-- name    : TsayQF.NoCommit.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:40.062929+00:00
-- url     : https://prove2.me/theorems/ff661b66-51c3-41a5-8a51-2e6cbf124b62
-- title:
--   Proposition 1, p. 1347 — without commitment the EM underproduces, Q*_NC < Q*_CC, and expected system profit is strictly suboptimal
-- statement:
--   Consider the supply chain of Tsay (1999): a retailer and a manufacturer (EM) with retail price $p$, transfer price $c$, production cost $m$, salvage value $u$ and goodwill loss $s$ satisfying
--   $$p > c > m > 0,\qquad u < m,\qquad s \ge 0 .$$
--   Market demand is $X = \mu + \varepsilon$, where the signal $\mu$ has a differentiable, strictly increasing distribution function $\Theta$ and finite variance, and $\varepsilon \sim N(0,\sigma_\varepsilon^2)$, $\sigma_\varepsilon \ge 0$, is independent of $\mu$. Let $z_\varepsilon = \Phi^{-1}\big((p+s-c)/(p+s-u)\big)$.
--
--   The retailer's forecast carries no commitment: the EM produces $Q$ before $\mu$ is observed, and the retailer then buys $\min[\mu + z_\varepsilon\sigma_\varepsilon, Q]$. Let $Q^*_{NC}$ be any production maximizing the EM's expected profit $\pi_{EM,NC}$, and $Q^*_{CC}$ any production maximizing the central planner's expected profit $\Pi_{CC}$. Then, for every such transfer price $c$,
--   $$Q^*_{NC} < Q^*_{CC} \qquad\text{and}\qquad \pi_{R,NC}(Q^*_{NC}) + \pi_{EM,NC}(Q^*_{NC}) < \Pi_{CC}(Q^*_{CC}).$$
--   That is, the EM underproduces relative to the optimal centralized solution, and the expected total system profit is strictly suboptimal.
--
--   This is the inefficiency result that motivates contracts beyond a linear transfer price, such as the quantity flexibility contract.
--
--   **Formalization Note** The two productions are stated as arbitrary maximizers of the respective expected profits over $\mathbb R$; the milestones show that maximizers exist and equal $\Theta^{-1}((c-m)/(c-u)) + z_\varepsilon\sigma_\varepsilon$ and $F^{-1}((p+s-m)/(p+s-u))$. $z_\varepsilon$ is a real $z$ with the hypothesis $\Phi(z) = (p+s-c)/(p+s-u)$. Finite variance of $\mu$ (the paper's "variance $\sigma_\mu^2$") makes every expectation integrable. The case $\sigma_\varepsilon = 0$ is included. The error stays normal, as in §3.3 (footnote 5 remarks normality is not needed).
-- source:
--   Tsay, The quantity flexibility contract and supplier-customer incentives, Management Science 45(10) (1999), p. 1347, Proposition 1

import Mathlib
import Definitions.Def_TsayQF_NoCommit_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TsayQF.NoCommit

theorem proposition_1 (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (v : ℝ≥0) (z : ℝ) (hz : cdf (gaussianReal 0 1) z = kR D) (Qnc Qcc : ℝ)
    (hnc : IsMaxOn (emProfit D ν v z) Set.univ Qnc)
    (hcc : IsMaxOn (ccProfit D ν v) Set.univ Qcc) :
    Qnc < Qcc ∧ systemProfit D ν v z Qnc < ccProfit D ν v Qcc := by sorry

end TsayQF.NoCommit
