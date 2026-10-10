-- Prove2me | Theorems.Thm_RiskSensMFG_Existence_proposition_1
-- name    : RiskSensMFG.Existence.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:40.680742+00:00
-- url     : https://prove2.me/theorems/f799ac1d-85d9-4d31-ac81-c8a8376198b3
-- title:
--   Proposition 1, p. 9 — Markov policies suffice: $\inf_{\pi\in\Pi}J_\mu(\pi)=\inf_{\pi\in\mathsf M}J_\mu(\pi)$
-- statement:
--   Throughout, $\mathsf X$ and $\mathsf A$ are Polish spaces with their Borel σ-fields, $\mathsf A$ is compact and nonempty, $(\mathsf X,\mathsf A,p,c,\mu_0)$ is a mean-field game model with discount factor $\beta\in(0,1)$, risk factor $\lambda>0$ and a measurable cost $c\ge 0$, and Assumption 1 holds: $c$ is continuous with $\|c\|\le K$, $p$ is weakly continuous in $(x,a,\mu)$, and there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with $\int w\,dp(\cdot|x,a,\mu)\le\alpha w(x)$ and $\int w\,d\mu_0<\infty$.
--
--   Let $\mu=(\mu_t)_{t\ge0}$ be any measure flow. Then restricting to Markov policies does not change the optimal risk-sensitive cost:
--   $$\inf_{\sigma\in\Pi}J_\mu(\sigma)=\inf_{\pi\in\mathsf M}J_\mu(\pi).$$
--   Equivalently: for every policy $\sigma$ and every $\delta>0$ there is a Markov policy $\pi$ with
--   $$J_\mu(\pi)\le J_\mu(\sigma)+\delta .$$
--
--   This is what allows the paper to work with Markov policies throughout §4 and to pass from optimality among Markov policies (Theorem 2) to optimality among all policies, as Definition 3 requires.
--
--   **Formalization Note** Only the first assertion of Proposition 1 is stated; the second, $\Lambda(\Pi)=\Lambda(\mathsf M)$, needs the flow map of a history-dependent policy and is not used for Theorem 1. The equality of infima is stated in the equivalent $\delta$-form ($\ge$ is immediate since Markov policies are policies). The paper states the proposition before Assumption 1 and omits its proof (“as in [38, Proposition 3.2]”); here it is stated under the paper's standing assumptions from p. 10 on, which make $J_\mu$ bounded. The standing assumptions of the paper's §3–§4 (Polish $\mathsf X$, $\mathsf A$; $\beta\in(0,1)$, $\lambda>0$, $c\ge0$ measurable; Assumption 1) are hypotheses. Nonemptiness of $\mathsf A$ is added: the paper uses it tacitly (with $\mathsf A=\emptyset$ there is no policy at all). The flow $\mu$ ranges over all of $\mathcal P(\mathsf X)^\infty$; the paper fixes $\mu\in\mathcal M$ (flows with $\mu_0$ prescribed), but the value at time $0$ of the flow enters only as a parameter of $p$ and $c$, so this is a harmless generalization.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 9, Proposition 1 (first sentence); proof omitted, cited to [38, Proposition 3.2]

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model

open MeasureTheory ProbabilityTheory

namespace RiskSensMFG.Existence

/-- Proposition 1 (p. 9), first assertion: for every measure flow `μ`,
`inf_{σ ∈ Π} J_μ(σ) = inf_{π ∈ M} J_μ(π)`, stated as: every policy is matched by a Markov policy
up to any `δ > 0`. -/
theorem proposition_1 {X A : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [Nonempty A] (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (μ : ℕ → PM X) (σ : Policy X A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ π : MarkovPolicy X A, J M μ π.toPolicy ≤ J M μ σ + δ := by sorry

end RiskSensMFG.Existence
