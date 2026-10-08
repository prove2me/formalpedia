-- Prove2me | Theorems.Thm_SchmidliRuin_Exist_theorem_2
-- name    : SchmidliRuin.Exist.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:54.336119+00:00
-- url     : https://prove2.me/theorems/76721bcf-7913-4943-bf89-3ec4cce9bf64
-- title:
--   Theorem 2, p. 900 — if G has a bounded density, (5) has a unique strictly decreasing solution g on [0, ∞)
-- statement:
--   Consider the classical risk model with premium rate $c>0$, Poisson claim intensity $\lambda>0$ and claim sizes $Y$ with continuous distribution function $G$, $G(0)=0$. The insurer invests in a risky asset with drift $\mu>0$ and volatility $\sigma>0$ and buys proportional reinsurance with retention $b\in[0,1]$ at premium rate $c(b)$. Here $c(b)$ is decreasing and continuous, $c(1)=0$, $\liminf_{b\uparrow1}c(b)/(1-b)>0$, and there is $\underline b>0$ with $c(b)>c$ for $b<\underline b$ and $c(b)\le c$ for $b\ge\underline b$.
--
--   **Theorem.** Suppose that $G$ has a bounded density. Then there is a unique strictly decreasing function $g$ on $[0,\infty)$ solving
--   $$
--   g(u)=\frac{1}{\dfrac{\mu^2}{2\sigma^2}\displaystyle\int_0^u\frac{dx}{\inf_{b\in[0,1]}\lambda\big(1-G(x/b)+\int_0^x(1-G((x-z)/b))g(z)\,dz\big)-(c-c(b))g(x)}+\dfrac{c}{\lambda}}\qquad(u\ge0).
--   $$
--
--   Equation (5) is the HJB equation of the problem of minimising the probability of ruin, rewritten for $g=f'$. By Theorem 1, $f(x)=1+\int_0^xg(z)\,dz$ normalised by $f(\infty)$ is the maximal survival probability, and the maximisers in (5) give the optimal investment and reinsurance strategy. Theorem 2 thus shows that the optimisation problem has a classical solution.
--
--   **Formalization Note.** Lean states existence and uniqueness separately. Uniqueness is equality on $[0,\infty)$, because the values of $g$ on $(-\infty,0)$ are irrelevant, so a unique-existence quantifier over functions $\mathbb R\to\mathbb R$ would be false. "Solving (5)" includes the existence of the integral in (5) at each $u$: $g$ integrable on $[0,u]$, the denominator non-zero on $(0,u)$, its reciprocal integrable. The parameters $\lambda,c$ are general; §4 normalises $\lambda=c=1$ by a change of time and monetary unit. $1-G(x/b)$ at $b=0$ is read as $\mathbb P[0\cdot Y>x]=0$. $c(b)$ is real-valued, which excludes the case $c(0)=\infty$ the paper allows when $\mathbb E[Y]<\infty$.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 900, Theorem 2

import Mathlib
import Definitions.Def_SchmidliRuin_Exist_Setting

namespace SchmidliRuin.Exist

open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics

/-- Theorem 2 (Schmidli 2002, p. 900): if the claim-size distribution has a bounded density, there
exists a unique strictly decreasing solution `g` of (5) on `[0, ∞)`. -/
theorem theorem_2
    (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : SchmidliRuin.Verif.ReinsPremium c cb) (hν : SchmidliRuin.Verif.ClaimLaw ν)
    (hdens : HasBoundedDensity ν) :
    (∃ g : ℝ → ℝ, StrictAntiOn g (Ici 0) ∧ SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g (Ici 0)) ∧
    ∀ g₁ g₂ : ℝ → ℝ,
      StrictAntiOn g₁ (Ici 0) → SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g₁ (Ici 0) →
      StrictAntiOn g₂ (Ici 0) → SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g₂ (Ici 0) →
      EqOn g₁ g₂ (Ici 0) := by sorry

end SchmidliRuin.Exist
