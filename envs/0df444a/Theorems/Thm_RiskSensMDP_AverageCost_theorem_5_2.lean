-- Prove2me | Theorems.Thm_RiskSensMDP_AverageCost_theorem_5_2
-- name    : RiskSensMDP.AverageCost.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:47.976657+00:00
-- url     : https://prove2.me/theorems/751cb1b6-2bee-4f86-8d6b-2bdf74f30b4f
-- title:
--   Theorem 5.2 — for γ ≥ 1 and a positive Harris recurrent MDP, a risk-neutral optimal stationary policy is optimal for the power-utility average cost (5.1)
-- statement:
--   Let $\gamma\ge1$ and $U(y)=y^\gamma$. Suppose the MDP is positive Harris recurrent: for every stationary policy, the corresponding state process is positive Harris recurrent. Let $\pi^*=(f^*,f^*,\dots)$ be an optimal stationary policy for the risk-neutral average cost problem, so that $\rho_{\pi^*}(x)\le\rho_\sigma(x)$ for all $\sigma\in\Pi$ and $x\in E$. Then $\pi^*$ is optimal for problem (5.1):
--   $$
--   J_{\pi^*}(x)\le J_\sigma(x)\quad\text{for every }\sigma\in\Pi\text{ and }x\in E,\qquad\text{hence}\qquad J_{\pi^*}(x)=J(x)=\inf_{\sigma\in\Pi}J_\sigma(x).
--   $$
--   The optimal policy does not depend on $\gamma$.
--
--   So under positive Harris recurrence, a decision maker who is risk averse in the sense of a convex power disutility of accumulated cost can use the classical risk-neutral average-cost optimal stationary policy. No new dynamic program has to be solved.
--
--   **Formalization Note** The hypotheses on $\pi^*$ do not mention $\gamma$, which is the formal content of "does not depend on $\gamma$". Positive Harris recurrence is assumed for every stationary policy, as in the paper, although a proof may need it only for $\pi^*$. Both the risk-neutral optimality of $\pi^*$ and the conclusion range over all history-dependent policies $\sigma\in\Pi$.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), p. 17, Theorem 5.2

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_Model
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_RiskSensMDP_AverageCost_Criterion

open MeasureTheory ProbabilityTheory Filter Finset

namespace RiskSensMDP.AverageCost

/-- Theorem 5.2 (p. 17): let `γ ≥ 1` and suppose the MDP is positive Harris recurrent. If
`π* = (f*, f*, …)` is an optimal stationary policy for the risk-neutral average cost problem, then
`π*` is optimal for problem (5.1) with `U(y) = y^γ`: `J_{π*}(x) ≤ J_σ(x)` for every `σ ∈ Π` and
`x ∈ E`, and so `J_{π*}(x) = J(x)`. -/
theorem theorem_5_2 {E A : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model E A) (γ : ℝ) (hγ : 1 ≤ γ) (hM : MDPPositiveHarris M)
    (fstar : StationaryRule M) (hopt : IsRiskNeutralOptimal M fstar) :
    (∀ (σ : Policy M) (x : E), powerAvgCost M γ fstar.toPolicy x ≤ powerAvgCost M γ σ x) ∧
    (∀ x : E, powerAvgCost M γ fstar.toPolicy x = optPowerAvgCost M γ x) := by sorry

end RiskSensMDP.AverageCost
