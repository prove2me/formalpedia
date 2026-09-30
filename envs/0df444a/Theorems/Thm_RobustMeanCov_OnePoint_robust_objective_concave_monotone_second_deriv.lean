-- Prove2me | Theorems.Thm_RobustMeanCov_OnePoint_robust_objective_concave_monotone_second_deriv
-- name    : RobustMeanCov.OnePoint.robust_objective_concave_monotone_second_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:48:13.027688+00:00
-- url     : https://prove2.me/theorems/076c9d7a-74eb-4444-a732-b864d6b98371
-- title:
--   Proposition 7 — concave utilities with monotone $u''$: $U(x)=u(\mu_x)+\lim u''\cdot\sigma_x^2/2$
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be concave and twice differentiable with a monotone second derivative $u''$. For $m\in\mathbb R$ and $s\ge0$ write $U(m,s)=\inf\{E_\nu[u] : \nu\in\mathbb M_{(m,s^2)}\}$ for the worst-case expected utility over all laws with mean $m$ and variance $s^2$; by Proposition 1 of the paper this is the robust objective $U(x)$ with $m=\mu_x$, $s=\sigma_x$.
--
--   **(a)** Suppose $u'$ is convex. Then $u''$ is nondecreasing and nonpositive, and exactly one of the following holds.
--
--   1. If $u''(y)\to L\in\mathbb R$ as $y\to-\infty$, then $u$ is integrable under every law of every class $\mathbb M_{(m,s^2)}$, $u$ has the one-point support property, and for all $m$ and all $s\ge 0$
--   $$
--   U(m,s)=u(m)+L\,\frac{s^2}{2},
--   $$
--   the infimum being a greatest lower bound.
--   2. If $u''(y)\to-\infty$ as $y\to-\infty$, then for all $m$ and all $s>0$ the value $U(m,s)$ is $-\infty$: for every $C\in\mathbb R$ some law in $\mathbb M_{(m,s^2)}$ under which $u$ is integrable has $E[u]<C$.
--
--   **(b)** Suppose $u'$ is concave. Then the same statements hold with the limit of $u''(y)$ as $y\to+\infty$ in place of $y\to-\infty$.
--
--   In both cases $U(x)=u(\mu_x)+\lim u''(y)\,\sigma_x^2/2$, read in $[-\infty,\infty)$. For the portfolio problem this reduces the robust objective of a prudent (convex $u'$) or imprudent (concave $u'$) risk-averse investor to a mean–variance criterion with the explicit risk weight $\tfrac12\lim u''$.
--
--   **Formalization Note** The paper's first sentence, "then $u$ has one-point support", is false when $\lim u''=-\infty$: for $u(y)=1-e^{-ay}$ (Example 3) no quadratic lies below $u$ on $\mathbb R$, so Definition 3 cannot hold. The one-point support conclusion is therefore stated only in the finite-limit case; the formula itself holds in both cases, with value $-\infty$ in the second. The infinite case requires $s>0$ (for $s=0$ the class is the point mass at $m$ and the value is $u(m)$). "Min" is read in the paper's wide sense of $\inf$ and is stated with `IsGLB` rather than a real infimum. The statement is made on the univariate class $\mathbb M_{(m,s^2)}$, which is $U(x)$ by Proposition 1. The hypothesis "monotone second derivative" is kept as printed although each of (a), (b) implies it.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 103, §3.2, Proposition 7; proof: pp. 110–111, Appendix, proof of Proposition 7

import Mathlib
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
import Definitions.Def_RobustMeanCov_OnePoint_OnePointSupport
open MeasureTheory Filter Topology

namespace RobustMeanCov.OnePoint

theorem robust_objective_concave_monotone_second_deriv (u : ℝ → ℝ)
    (hconc : ConcaveOn ℝ Set.univ u) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u))
    (hmono : Monotone (deriv (deriv u)) ∨ Antitone (deriv (deriv u))) :
    -- (a) `u'` convex: the limit of `u''` at `-∞`
    (ConvexOn ℝ Set.univ (deriv u) →
      (∀ L : ℝ, Tendsto (deriv (deriv u)) atBot (𝓝 L) →
        (∀ m s : ℝ, 0 ≤ s → ∀ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), Integrable u ν) ∧
        (∀ m s : ℝ, 0 ≤ s →
          IsGLB {v : ℝ | ∃ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), ∫ y, u y ∂ν = v}
            (u m + L * s ^ 2 / 2)) ∧
        OnePointSupport u) ∧
      (Tendsto (deriv (deriv u)) atBot atBot →
        ∀ m s : ℝ, 0 < s → ∀ C : ℝ,
          ∃ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), Integrable u ν ∧ ∫ y, u y ∂ν < C)) ∧
    -- (b) `u'` concave: the limit of `u''` at `+∞`
    (ConcaveOn ℝ Set.univ (deriv u) →
      (∀ L : ℝ, Tendsto (deriv (deriv u)) atTop (𝓝 L) →
        (∀ m s : ℝ, 0 ≤ s → ∀ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), Integrable u ν) ∧
        (∀ m s : ℝ, 0 ≤ s →
          IsGLB {v : ℝ | ∃ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), ∫ y, u y ∂ν = v}
            (u m + L * s ^ 2 / 2)) ∧
        OnePointSupport u) ∧
      (Tendsto (deriv (deriv u)) atTop atBot →
        ∀ m s : ℝ, 0 < s → ∀ C : ℝ,
          ∃ ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2), Integrable u ν ∧ ∫ y, u y ∂ν < C)) := by sorry

end RobustMeanCov.OnePoint
