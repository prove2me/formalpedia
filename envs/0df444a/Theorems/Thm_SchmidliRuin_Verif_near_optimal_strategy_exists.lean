-- Prove2me | Theorems.Thm_SchmidliRuin_Verif_near_optimal_strategy_exists
-- name    : SchmidliRuin.Verif.near_optimal_strategy_exists
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T00:16:00.556552+00:00
-- url     : https://prove2.me/theorems/5dd5e199-0a28-4849-8037-6231b0bb527b
-- title:
--   Theorem 1, p. 896–897 — lower bound δ(u) ≥ f(u)/f(∞): ε-optimal admissible strategies exist
-- statement:
--   In the setting of Schmidli's verification theorem (classical risk model with Poisson claim arrivals of rate $\lambda>0$, continuous claim law $G$ with $G(0)=0$, premium rate $c>0$, investment in a Black–Scholes asset with drift $\mu>0$ and volatility $\sigma>0$, proportional reinsurance with premium rate $c(b)$ satisfying the standing assumption of p. 891), let $f$ satisfy the analytic hypotheses of Theorem 1: $f=0$ on $(-\infty,0)$, $f\ge 0$, $f$ strictly increasing and continuous on $[0,\infty)$, $C^2$ on $(0,\infty)$, and solving the HJB equation (1) at every $u>0$. Suppose $f(x)\to L$ as $x\to\infty$ with $L$ finite.
--
--   Then, for every initial capital $u\ge 0$ and every $\varepsilon>0$, there is an admissible strategy $(A,b)$ with surplus process $X$ from $u$ whose survival probability satisfies
--   $$\delta^{Ab}(u) = \mathbb P[\tau^{Ab}=\infty] > \frac{f(u)}{L}-\varepsilon .$$
--
--   This is the lower-bound half of the identity $\delta(u)=f(u)/f(\infty)$ in Theorem 1 (p. 896): it says $\delta(u)\ge f(u)/f(\infty)$, where $\delta$ is the supremum of the survival probabilities over all admissible strategies. In the paper this half is obtained on p. 897 from the sentence "This yields $\delta^{Ab}(u)\le f(u)/f(\infty)$, with equality for $\delta^{A^*b^*}(u)$", i.e. by evaluating the survival probability of the surplus process $X^*$ that follows the feedback strategy $A_t=A^*(X_{t-})$, $b_t=b^*(X_{t-})$; the paper takes the existence of this process (as an admissible strategy from every $u\ge0$) for granted. The milestone `survival_le_and_eq` supplies the upper bound and the equality for every feedback process from $u>0$, but not the existence of an (approximately) optimal admissible strategy, which is what this statement isolates. The $\varepsilon$-form avoids assuming that the supremum is attained.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 896, Theorem 1 (the identity δ(u) = f(u)/f(∞), lower-bound half), proof on p. 897 ("with equality for δ^{A*b*}(u)")

import Mathlib
import Definitions.Def_SchmidliRuin_Verif_Setting
import Definitions.Def_SchmidliRuin_Verif_Model

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SchmidliRuin.Verif

theorem near_optimal_strategy_exists {Ω : Type*} [MeasurableSpace Ω] (B : RiskBasis Ω)
    (hB : B.IsValid) (c mu sigma : ℝ) (hc : 0 < c) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (cb : ℝ → ℝ) (hcb : ReinsPremium c cb)
    (f : ℝ → ℝ) (hf : IsHJBSolution c B.lam mu sigma cb B.ν f)
    (L : ℝ) (hL : Tendsto f atTop (𝓝 L)) (u : ℝ) (hu : 0 ≤ u) (ε : ℝ) (hε : 0 < ε) :
    ∃ A b X : ℝ≥0 → Ω → ℝ, IsAdmissible B c mu sigma cb u A b X ∧
      f u / L - ε < survivalProb B X := by sorry

end SchmidliRuin.Verif
