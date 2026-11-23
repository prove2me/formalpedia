-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_Supplement_theorem_1
-- name    : SalesRebate.NoIncreasing.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:15:30.257731+00:00
-- url     : https://prove2.me/theorems/242ea477-f92a-49a0-82c7-8f0761ce5f50
-- title:
--   Theorem 1, p. 15 (PDF 15) — optima of (3) are full-refund-or-nothing; with σ fixed, l = Ω(1/σϵ) and the best l-interval profit tends to the no-reward profit
-- statement:
--   Let $(\theta,\sigma_\theta,\sigma_\epsilon)$ be a valid model of §II ($v\sim N(\theta,\sigma_\theta^2)$ the common quality, $\epsilon_i\sim N(0,\sigma_\epsilon^2)$ the tastes, $\sigma_\theta,\sigma_\epsilon>0$), with $\sigma^2=\sigma_\epsilon^2+\sigma_\theta^2$, $\tau=\sigma_\theta^2/\sigma^2$, $\sigma_v=\sigma_\epsilon\sigma_\theta/\sigma$ and $\mu_c=\tau c+(1-\tau)\theta$, and let $p$ be a market price satisfying Assumption 1 ($p$ maximizes $x\Phi((\theta-x)/\sigma)$ over $x\ge0$). Here $\Phi,\phi$ are the standard normal CDF and density, $\mathbb E_{v\mid v_i=x}$ is the expectation under the posterior $N(\tau x+(1-\tau)\theta,\sigma_v^2)$, and the expected profit of a reward $\hat r$ (a function of the quality) with cutoff $c$ is (2): $\mathbb E_v[\Pi(p,\hat r)]=\mathbb E_v[(p-\hat r(v))\Phi((v-c)/\sigma_\epsilon)]$.
--
--   Problem (3) maximizes the expected profit over pairs $(\hat r,c)$ with $\hat r\in L^\infty(\mathbb R;[0,p])$ such that the threshold strategy with cutoff $c$ is an equilibrium (1). A **full-refund-or-nothing policy with $l$ intervals** is a reward of the form
--   $$\hat r(v)=p\times\sum_{j=1}^{l}\mathbf 1\{w_L^j\le v\le w_H^j\}$$
--   (almost everywhere, endpoints possibly infinite). Then:
--
--   1. Problem (3) has an optimal pair. For every fixed $l$, its restriction to full-refund policies with at most $l$ intervals also has an optimal pair. The reward $\hat r^*$ of every optimal pair is a full-refund-or-nothing policy with some finite number $l$ of intervals.
--
--   Now fix $\theta$ and the total uncertainty $\sigma>0$, let $\sigma_\epsilon\in(0,\sigma)$ and $\sigma_\theta=\sqrt{\sigma^2-\sigma_\epsilon^2}$, and let $p$ satisfy Assumption 1 (the same $p$ for every $\sigma_\epsilon$, since $\sigma$ is fixed).
--
--   2. There are $C>0$ and $\delta>0$ such that for every $\sigma_\epsilon<\delta$, every optimal pair of (3) and every representation of its reward as a full-refund-or-nothing policy with $l$ intervals,
--   $$l\ \ge\ \frac{C}{\sigma_\epsilon},\qquad\text{i.e. } l=\Omega(1/\sigma_\epsilon).$$
--   3. For every fixed $l$, the best expected profit over feasible pairs of (3) whose reward is a full-refund-or-nothing policy with $l$ intervals tends to the no-reward profit:
--   $$\lim_{\sigma_\epsilon\to0^+}\ \sup\big\{\mathbb E_v[\Pi(p,\hat r)]\big\}\ =\ p\,\Phi\Big(\frac{\theta-p}{\sigma}\Big).$$
--
--   The theorem says the optimal sales-based reward program refunds the full price on finitely many quality intervals, that as taste heterogeneity vanishes it needs ever more intervals, and that any bounded number of intervals gains nothing in the limit.
--
--   **Formalization Note** The three parts are the conjuncts of one statement; part 1 is posed for every valid model, parts 2–3 along the family `famModel θ σ s`. Optimal values are suprema over nonempty sets bounded by $p$.
--
--   Differences from the source:
--   - encoding: the optimization problem in (III) → problem (3) of p. 10 (Feasible3 / IsOptimal3 / optValue3); reason: (III) is a broken cross-reference: the paper has no display (III), and the text around it (pp. 13, 17, 20) refers to the infinite-dimensional problem (3)
--   - reading: 'the optimal reward program r̂*(·) cast as the solution of (III) is of the form …' → an optimal pair exists, and every optimal pair has the stated form; reason: the definite article presupposes an optimum; posing only 'every optimum has the form' would be vacuous if none existed, so existence is part of the claim (the appendix proves it)
--   - encoding: r̂*(v) = p × Σ_{j=1}^{l} 1{wjL ≤ v ≤ wjH} for r̂* ∈ L∞ → IsFullRefundPolicy p l r̂: equality almost everywhere (Lebesgue), endpoints in EReal, empty intervals allowed; reason: r̂ is an element of L∞, so its form is determined up to null sets; infinite endpoints are allowed on p. 13 (w1L = −∞); an empty interval adds nothing, so 'l intervals' and 'at most l intervals' coincide
--   - reading: i) the number of intervals l tends to infinity, 1/σϵ = O(l), l = Ω(1/σϵ) → ∃ C > 0, ∃ δ > 0, for every σϵ ∈ (0, min(σ, δ)), every optimum of (3) and every representation of it with l intervals, C/σϵ ≤ l; reason: the derivation on p. 15 concludes lim inf_{σϵ→0} lσϵ > 0 for the optimal program; a bound on every representation is a bound on the least l, and l → ∞ follows
--   - reading: ii) for fixed l, the expected profit of the optimal program with l full-refund intervals approaches that of the no reward case → for every valid M, Assumption-1 p and l, a (3)-feasible full-refund pair with at most l intervals attains the largest profit in that class; along famModel the resulting optimal value tends to pΦ((θ − p)/σ) as s → 0⁺; reason: the source says the optimal program with l intervals, which includes attainment; IsOptimalRefund restores this clause, while optValueRefund expresses its value without choosing an optimizer; empty intervals pad any representation, including the no-reward case
--   - encoding: fixing σ² = σθ² + σϵ² and letting σϵ → 0 → the family famModel θ σ s = (θ, √(σ² − s²), s) with 0 < σ, the limit along s → 0⁺ (𝓝[>] 0), and the Assumption-1 hypothesis for every member with s ∈ (0, σ); reason: for 0 < s < σ the family has total uncertainty exactly σ, so Assumption 1 fixes the same p for every member; the paper's σϵ → 0 is one-sided because σϵ > 0
--   - encoding: standing assumptions of §II (Gaussian laws) and Assumption 1 for the price p → hM : M.Valid (σθ, σε > 0) and hp : M.IsMarketPrice p (maximization clause over x ≥ 0) from the published Setting; reason: the page's Gaussian laws and its divisions by σε, σθ presuppose positive deviations, and p is defined by Assumption 1 throughout the paper; no instance of the paper's setting is excluded
--   - generalization: a fixed number l of refund intervals → l : ℕ, including l = 0; reason: the zero-interval class consists of the no-reward policy almost everywhere, with equilibrium cutoff p; its optimal profit equals the no-reward benchmark for every positive deviation, so the added case satisfies the limit identically
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 15, Theorem 1 (problem (3), p. 10; full-refund policy, p. 13)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems

namespace SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

theorem theorem_1 :
    (∀ (M : Model), M.Valid → ∀ p : ℝ, M.IsMarketPrice p →
      (∃ rhat c, IsOptimal3 M p rhat c) ∧
        (∀ rhat c, IsOptimal3 M p rhat c → ∃ l : ℕ, IsFullRefundPolicy p l rhat) ∧
        (∀ l : ℕ, ∃ rhat c, IsOptimalRefund M p l rhat c)) ∧
    (∀ θ σ p : ℝ, 0 < σ → (∀ s ∈ Set.Ioo 0 σ, (famModel θ σ s).IsMarketPrice p) →
      (∃ C > 0, ∃ δ > 0, ∀ s ∈ Set.Ioo 0 σ, s < δ → ∀ rhat c,
        IsOptimal3 (famModel θ σ s) p rhat c → ∀ l : ℕ, IsFullRefundPolicy p l rhat →
          C / s ≤ (l : ℝ)) ∧
      ∀ l : ℕ, Tendsto (fun s => optValueRefund (famModel θ σ s) p l) (𝓝[>] 0)
        (𝓝 (p * stdNormalCDF ((θ - p) / σ)))) := by sorry

end SalesRebate.NoIncreasing.Supplement
