-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_Supplement_lemma_3
-- name    : SalesRebate.NoIncreasing.Supplement.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T03:21:53.291751+00:00
-- url     : https://prove2.me/theorems/d8cc76d9-ae64-4786-b0d3-96b023cfbfbe
-- title:
--   Lemma 3, p. 19 (PDF 19) — if r̂ : R → [0, p] is piecewise C¹ with |r̂′| ≤ 1/τ, the expected payoff of adoption is increasing in the valuation
-- statement:
--   Let $(\theta,\sigma_\theta,\sigma_\epsilon)$ be a valid model of §II, $\tau=\sigma_\theta^2/(\sigma_\epsilon^2+\sigma_\theta^2)$, $p$ a price, and $\hat r:\mathbb R\to[0,p]$ a continuous, piecewise continuously differentiable reward (a function of the quality) with
--   $$\Big|\frac{d}{dv}\hat r(v)\Big|\ \le\ \frac1\tau$$
--   away from its break points (finitely many in every bounded interval). Then the expected payoff of adoption
--   $$x\ \mapsto\ x-p+\mathbb E_{v\mid v_i=x}[\hat r(v)]$$
--   is (weakly) increasing in the valuation $x$, where $\mathbb E_{v\mid v_i=x}$ is the expectation under the posterior $N(\tau x+(1-\tau)\theta,\sigma_v^2)$.
--
--   As with Lemma 2, the conclusion reduces the equilibrium constraints (1) to the indifference equation, so the optimum of the rate-constrained problem (Theorem 4) is feasible for problem (3) (Theorem 5 ii).
--
--   **Formalization Note** Continuity is part of "piecewise continuously differentiable" here; see the differences below.
--
--   Differences from the source:
--   - reading: the expected payoff of adoption, assuming a monotone symmetric (threshold) strategy, is increasing with the valuations → Monotone (fun x => x − p + E_{v|vi=x}[r̂(v)]) for the given reward r̂ of the quality; reason: under a threshold strategy the reward is a fixed function r̂ of the quality (p. 10) and the payoff of adoption at valuation vi is vi − p + E_{v|vi}[r̂(v)]; 'increasing' is weak, the convention of the published mission, and is what the single-crossing argument (p. 18) uses
--   - reading: r̂ : R → [0, p] piece-wise continuously differentiable with |d/dv r̂(v)| ≤ 1/τ → IsRateConstrained M r̂: r̂ continuous, C¹ off a set D with finitely many points in every bounded interval, finite left and right derivative limits at every point of D, |deriv r̂| ≤ 1/τ off D; reason: the paper uses continuous piecewise-C¹ rewards in Lemma 3 and a piecewise-continuous control u = −r̂′ in (29), p. 34; the finite one-sided derivative limits restore that class. Continuity rules out jumps, which would invalidate Lemma 3. No behavior at infinity is added to the main-text class
--   - encoding: standing assumptions of §II → hM : M.Valid (σθ, σε > 0); reason: the Gaussian laws and τ presuppose positive deviations
--   - generalization: the standing Assumption-1 market price p → an arbitrary price p for which the bounded reward hypotheses hold; reason: the purchase payoff differs by the additive constant −p, which does not affect monotonicity; the proof on pp. 29–30 or 33–34 uses no price-optimality assumption. Specializing to a market price recovers every source instance
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 19, Lemma 3

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems

namespace SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

theorem lemma_3 (M : Model) (hM : M.Valid) (p : ℝ) (rhat : ℝ → ℝ)
    (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) (hrate : IsRateConstrained M rhat) :
    Monotone (fun x => x - p + M.condReward rhat x) := by sorry

end SalesRebate.NoIncreasing.Supplement
