-- Prove2me | Theorems.Thm_ProjectOutsourcing_SingleTask_prop1_tb
-- name    : ProjectOutsourcing.SingleTask.prop1_tb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:13.774808+00:00
-- url     : https://prove2.me/theorems/ffe96509-799d-48f1-8c87-2e5865588e9f
-- title:
--   Proposition 1 (TB), p. 11, restated p. 12 — TB coordinates exactly when θΠ* is a value of δ^TB_S on [0, ∞); the printed [δ̲^TB_S/Π*, 1] when the min in (4) is attained
-- statement:
--   Under the standing assumptions of Section 3, let $r^*$ be the system-optimal work rate, $\Pi^*=\Pi(r^*)$, and let $\delta^{TB}_S(\beta)$ be defined by (4). Then for the time-based incentive contract:
--
--   1. the set of bargaining powers at which TB coordinates the system is
--   $$\Phi^{TB}=\big\{\theta\in[0,1]:\ \delta^{TB}_S(\beta)=\theta\Pi^*\ \text{for some }\beta\ge 0\big\};$$
--   2. if the minimum $\underline\delta^{TB}_S=\min_{\beta\ge0}\delta^{TB}_S(\beta)$ is attained, then $\Phi^{TB}=[\underline\delta^{TB}_S/\Pi^*,1]$;
--   3. for $\theta\in\Phi^{TB}$, every solution of Problem B (3) has terms $\hat\beta^{TB}\ge0$ with $\delta^{TB}_S(\hat\beta^{TB})=\theta\Pi^*$ and
--   $$\hat p^{TB}=\frac{\alpha\,\mathbb E_Z[Ze^{-\alpha Z/r^*}]}{(\alpha+\hat\beta^{TB})\,\mathbb E_Z\big[Ze^{-(\alpha+\hat\beta^{TB})Z/r^*}\big]}\,Q ;$$
--   4. for $\theta\in[0,1]\setminus\Phi^{TB}$, no solution of Problem B under TB induces a system-optimal work rate.
--
--   The quantity $\delta^{TB}_S(\beta)$ is the subcontractor's profit when the time-based contract with parameter $\beta$ is tuned to induce $r^*$. The statement says that TB coordinates exactly when the subcontractor's bargaining power is high enough for his Nash share $\theta\Pi^*$ to be such a profit.
--
--   **Formalization Note** The page prints $\Phi^{TB}=[\underline\delta^{TB}_S/\Pi^*,1]$ with $\underline\delta^{TB}_S=\min_{\beta\ge0}\delta^{TB}_S(\beta)$. In the paper's Example 1 the minimum is not attained: $\delta^{TB}_S$ is strictly decreasing and only approaches its infimum. There the printed closed interval would include an endpoint at which no term coordinates. The set is therefore stated as $\{\theta\in[0,1]:\theta\Pi^*\in\delta^{TB}_S([0,\infty))\}$, which matches the page's own definition of $\hat\beta^{TB}$ as a root of $\delta^{TB}_S(\beta)=\theta\Pi^*$ and the p. 12 phrase "above the threshold". The printed interval is also stated, under the hypothesis that the minimum is attained. Uniqueness of the root $\hat\beta^{TB}$ is not claimed. "Coordinates" means that a solution exists and every solution induces the system-optimal rate.
-- source:
--   Hou, Lu, Deng, Shen, Coordinating Project Outsourcing through Bilateral Contract Negotiations, author manuscript (SSRN 3443865; MSOM, doi:10.1287/msom.2020.0911), p. 11, Proposition 1 (part TB), (4); restatement p. 12

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting

namespace ProjectOutsourcing.SingleTask

theorem prop1_tb (M : Model) (hM : M.Valid) (rStar : ℝ) (hr : IsSystemOpt M rStar) :
    Phi M .TB =
        {θ | θ ∈ Set.Icc 0 1 ∧ ∃ β, 0 ≤ β ∧ deltaTB M rStar β = θ * sysProfit M rStar} ∧
      (∀ β₀, 0 ≤ β₀ → IsMinOn (deltaTB M rStar) (Set.Ici 0) β₀ →
        Phi M .TB = Set.Icc (deltaTB M rStar β₀ / sysProfit M rStar) 1) ∧
      (∀ θ ∈ Phi M .TB, ∀ x, IsNashSol M .TB θ x →
        0 ≤ x.1.2 ∧ deltaTB M rStar x.1.2 = θ * sysProfit M rStar ∧
          x.1.1 = M.alpha * discZ M M.alpha rStar /
            ((M.alpha + x.1.2) * discZ M (M.alpha + x.1.2) rStar) * M.Q) ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, θ ∉ Phi M .TB → ∀ x, IsNashSol M .TB θ x →
        ¬ IsSystemOpt M x.2) := by sorry

end ProjectOutsourcing.SingleTask
