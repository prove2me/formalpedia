-- Prove2me | Theorems.Thm_SchmidliRuin_Verif_theorem_1
-- name    : SchmidliRuin.Verif.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:17.695608+00:00
-- url     : https://prove2.me/theorems/245d8e5e-b047-4845-95bb-5f67039d7a6c
-- title:
--   Theorem 1, p. 896 — an increasing C² solution f of the HJB (1) is bounded, δ(u) = f(u)/f(∞), and A*(X_{t−}), b*(X_{t−}) is optimal
-- statement:
--   Consider the classical risk model with claim intensity $\lambda>0$, continuous claim-size distribution $G$ with $G(0)=0$ and premium rate $c>0$, in which the insurer may invest an amount $A_t$ in a risky asset with drift $\mu>0$ and volatility $\sigma>0$ and buy proportional reinsurance with retention $b_t\in[0,1]$ at premium rate $c(b_t)$, where $c(b)$ satisfies the standing assumption of p. 891. Let $\delta(u)$ be the maximal survival probability from initial capital $u$.
--
--   Let $f:\mathbb R_+\to\mathbb R_+$ be strictly increasing, continuous on $[0,\infty)$, twice continuously differentiable on $(0,\infty)$, with $f(u)=0$ for $u<0$, and solving the Hamilton–Jacobi–Bellman equation
--   $$\sup_{b\in[0,1]}\sup_{A\ge0}\Big[\tfrac12\sigma^2A^2f''(u)+(c-c(b)+\mu A)f'(u)+\lambda\big(\mathbb E[f(u-bY)]-f(u)\big)\Big]=0$$
--   at every $u>0$. Then:
--
--   1. $f$ is bounded;
--   2. $f(\infty)=\lim_{x\to\infty}f(x)$ is a positive real number and, for every $u\ge0$,
--   $$\delta(u)=\frac{f(u)}{f(\infty)};$$
--   3. the feedback strategy $A_t=A^*(X_{t-})$, $b_t=b^*(X_{t-})$ is optimal, where $A^*(x)=-\mu f'(x)/(\sigma^2f''(x))$ is given by (2) and $b^*(x)$ is a measurable argument maximising the left-hand side of the HJB equation: every admissible surplus process from $u>0$ that follows this rule has survival probability $\delta(u)$.
--
--   This is the verification theorem of the paper: a smooth increasing solution of the HJB equation, normalised by its limit, is the maximal survival probability, and its maximisers give the optimal investment and reinsurance strategy.
--
--   **Formalization Note** "Twice continuously differentiable" is read on $(0,\infty)$ and (1) is required for $u>0$: the solutions the theorem refers to, $f=1+\int_0^xg$, have $f''(0+)=-\infty$ (p. 895). The second sentence of the theorem ("This will be the case for $f(x)=1+\int_0^xg(z)\,dz$, …") and the last ("there is at most one … solution to (1) with $f(0)=1$") are the separate items `theorem_1_bridge` and `theorem_1_uniqueness`. The paper does not prove that a surplus process following the feedback rule exists (its proof begins "Let us start by considering the process $\{X^*_t\}$ following the optimal strategy"), so part 3 is stated for every such process and is vacuous if there is none. Part 3 is stated for $u>0$, as in the proof ($0<\varepsilon<u$); the controls at non-positive pre-jump surplus are left free. Maximising the whole bracket of (1) in $b$ gives the same $b^*$ as maximising $(c-c(b))f'(x)+\lambda(\mathbb E[f(x-bY)]-f(x))$, because the maximum over $A$ does not depend on $b$. The model includes independence of the Brownian motion from the claims and a real-valued $c(b)$ (so $c(0)<\infty$); see the `Model` and `Setting` definitions.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 896, Theorem 1

import Mathlib
import Definitions.Def_SchmidliRuin_Verif_Setting
import Definitions.Def_SchmidliRuin_Verif_Model

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SchmidliRuin.Verif

theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (B : RiskBasis Ω) (hB : B.IsValid)
    (c mu sigma : ℝ) (hc : 0 < c) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (cb : ℝ → ℝ) (hcb : ReinsPremium c cb)
    (f : ℝ → ℝ) (hf_neg : ∀ x < 0, f x = 0) (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hf_mono : StrictMonoOn f (Ici 0)) (hf_cont : ContinuousOn f (Ici 0))
    (hf_C2 : ContDiffOn ℝ 2 f (Ioi 0))
    (hf_hjb : ∀ u > 0, SolvesHJB c B.lam mu sigma cb B.ν f u) :
    BddAbove (f '' Ici 0) ∧
    (∃ L : ℝ, 0 < L ∧ Tendsto f atTop (𝓝 L) ∧
      ∀ u, 0 ≤ u → valueFn B c mu sigma cb u = f u / L) ∧
    (∀ bstar : ℝ → ℝ, IsBStar c B.lam cb B.ν f bstar →
      ∀ u, 0 < u → ∀ A b X : ℝ≥0 → Ω → ℝ,
        IsAdmissible B c mu sigma cb u A b X → FollowsFeedback mu sigma f bstar u A b X →
        survivalProb B X = valueFn B c mu sigma cb u) := by sorry

end SchmidliRuin.Verif
