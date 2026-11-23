-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_Supplement_theorem_5
-- name    : SalesRebate.NoIncreasing.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:22:31.79213+00:00
-- url     : https://prove2.me/theorems/a9334aa3-f452-444d-aa18-3afef44ad5d5
-- title:
--   Theorem 5, p. 22 (PDF 22) — (i) if σϵ/σθ ≥ p/(√(2π)σ) the spread-constrained optimum solves (3); (ii) with σ fixed, the rate-constrained optimum is asymptotically optimal
-- statement:
--   Let $(\theta,\sigma_\theta,\sigma_\epsilon)$ be a valid model of §II ($v\sim N(\theta,\sigma_\theta^2)$ the common quality, $\epsilon_i\sim N(0,\sigma_\epsilon^2)$ the tastes, $\sigma_\theta,\sigma_\epsilon>0$), with $\sigma^2=\sigma_\epsilon^2+\sigma_\theta^2$, $\tau=\sigma_\theta^2/\sigma^2$, $\sigma_v=\sigma_\epsilon\sigma_\theta/\sigma$ and $\mu_c=\tau c+(1-\tau)\theta$, and let $p$ be a market price satisfying Assumption 1 ($p$ maximizes $x\Phi((\theta-x)/\sigma)$ over $x\ge0$). Here $\Phi,\phi$ are the standard normal CDF and density, $\mathbb E_{v\mid v_i=x}$ is the expectation under the posterior $N(\tau x+(1-\tau)\theta,\sigma_v^2)$, and the expected profit of a reward $\hat r$ (a function of the quality) with cutoff $c$ is (2): $\mathbb E_v[\Pi(p,\hat r)]=\mathbb E_v[(p-\hat r(v))\Phi((v-c)/\sigma_\epsilon)]$.
--
--   Problem (3), the spread-constrained (SC) problem of Theorem 3 and the rate-constrained (RC) problem of Theorem 4 are as defined in `SalesRebate.NoIncreasing.Supplement.Problems`.
--
--   1. If
--   $$\frac{\sigma_\epsilon}{\sigma_\theta}\ \ge\ \frac{p}{\sqrt{2\pi}\,\sigma},$$
--   then the SC problem has an optimal pair, and every optimal pair of the SC problem is also an optimal pair of problem (3).
--   2. Fix $\theta$ and the total uncertainty $\sigma>0$, let $\sigma_\theta=\sqrt{\sigma^2-\sigma_\epsilon^2}$ for $\sigma_\epsilon\in(0,\sigma)$, and let $p$ satisfy Assumption 1. Writing $V_{RC}(\sigma_\epsilon)$ and $V^*(\sigma_\epsilon)$ for the optimal values of the RC problem and of problem (3),
--   $$\lim_{\sigma_\epsilon\to0^+}\frac{V_{RC}(\sigma_\epsilon)}{V^*(\sigma_\epsilon)}=1.$$
--
--   Part 1 says that when taste heterogeneity is large enough the simple step program loses nothing; part 2 says that the saturated linear program is asymptotically optimal when the uncertainty comes mainly from the common quality.
--
--   **Formalization Note** $V^*(\sigma_\epsilon)\ge p\Phi((\theta-p)/\sigma)>0$ (the no-reward pair is feasible and Assumption 1 forces $p>0$), so the ratio has a positive denominator.
--
--   Differences from the source:
--   - encoding: the optimization problem in (III) → problem (3) of p. 10 (Feasible3 / IsOptimal3 / optValue3); reason: (III) is a broken cross-reference: the paper has no display (III), and the text around it (pp. 13, 17, 20) refers to the infinite-dimensional problem (3)
--   - reading: i) the spread-constrained program r̂*SC characterized in Theorem 3 is optimal, i.e. also the solution to (III) → an optimal pair of the SC problem exists, and every optimal pair of the SC problem is an optimal pair of problem (3); reason: 'the program characterized in Theorem 3' is an optimum of the SC problem, whose existence Theorem 3 asserts; being 'the solution to (3)' means being feasible for (3) with the largest profit
--   - reading: ii) lim_{σϵ→0} Ev[Π(p, r̂*RC(v))]/Ev[Π(p, r̂*(v))] = 1 → optValueRC (famModel θ σ s) p / optValue3 (famModel θ σ s) p → 1 as s → 0⁺; reason: r̂*RC and r̂* are optima of the RC problem and of (3), so their profits are the two optimal values; the suprema need no choice of optimizer
--   - encoding: fixing σ² = σθ² + σϵ² and letting σϵ → 0 → the family famModel θ σ s = (θ, √(σ² − s²), s) with 0 < σ, the limit along s → 0⁺ (𝓝[>] 0), and the Assumption-1 hypothesis for every member with s ∈ (0, σ); reason: for 0 < s < σ the family has total uncertainty exactly σ, so Assumption 1 fixes the same p for every member; the paper's σϵ → 0 is one-sided because σϵ > 0
--   - encoding: standing assumptions of §II (Gaussian laws) and Assumption 1 for the price p → hM : M.Valid (σθ, σε > 0) and hp : M.IsMarketPrice p (maximization clause over x ≥ 0) from the published Setting; reason: the page's Gaussian laws and its divisions by σε, σθ presuppose positive deviations, and p is defined by Assumption 1 throughout the paper; no instance of the paper's setting is excluded
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 22, Theorem 5

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems

namespace SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

theorem theorem_5 :
    (∀ (M : Model), M.Valid → ∀ p : ℝ, M.IsMarketPrice p →
      p / (Real.sqrt (2 * Real.pi) * M.σ) ≤ M.σε / M.σθ →
      (∃ rhat c, IsOptimalSC M p rhat c) ∧
        ∀ rhat c, IsOptimalSC M p rhat c → IsOptimal3 M p rhat c) ∧
    (∀ θ σ p : ℝ, 0 < σ → (∀ s ∈ Set.Ioo 0 σ, (famModel θ σ s).IsMarketPrice p) →
      Tendsto (fun s => optValueRC (famModel θ σ s) p / optValue3 (famModel θ σ s) p)
        (𝓝[>] 0) (𝓝 1)) := by sorry

end SalesRebate.NoIncreasing.Supplement
