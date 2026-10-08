-- Prove2me | Theorems.Thm_PGLandscape_GradDom_loss_gradient_dominated
-- name    : PGLandscape.GradDom.loss_gradient_dominated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:51.081003+00:00
-- url     : https://prove2.me/theorems/edac68b6-df02-40f3-bbce-047ffc41e285
-- title:
--   Theorem 2, p. 16 — under Conditions 0, 1, 2.B, ℓ is (κ_ρ c/(1−γ), κ_ρ µ/(1−γ))-gradient dominated
-- statement:
--   Let $\Pi_\Theta=\{\pi_\theta:\theta\in\Theta\}$ be a parameterized policy class over a convex set $\Theta\subseteq\mathbb R^d$ in a discounted Markov decision process with an optimal policy $\pi^*$, and let $\ell(\theta)$ be the normalized discounted loss of $\pi_\theta$. Suppose
--
--   1. Condition 0 (differentiability of the weighted policy iteration objective),
--   2. Condition 1 (closure of $\Pi_\Theta$ under policy improvement),
--   3. Condition 2.B with constants $c>0$, $\mu\ge0$: for every $\pi\in\Pi_\Theta$, $\theta\mapsto\mathcal B(\theta\mid\eta_\pi,J_\pi)$ is $(c,\mu)$-gradient dominated over $\Theta$,
--
--   and let $\kappa>0$ satisfy (13). Then $\ell$ is
--   $$\Big(\frac{\kappa}{1-\gamma}\cdot c,\ \frac{\kappa}{1-\gamma}\cdot\mu\Big)\text{-gradient dominated over }\Theta,$$
--   that is, for every $\theta\in\Theta$,
--   $$\min_{\theta'\in\Theta}\ell(\theta')\ \ge\ \ell(\theta)+\min_{\theta'\in\Theta}\Big[\frac{\kappa c}{1-\gamma}\langle\nabla\ell(\theta),\theta'-\theta\rangle+\frac{\kappa\mu}{2(1-\gamma)}\|\theta-\theta'\|_2^2\Big].$$
--
--   Gradient dominance of the single-period problem is thus inherited by the non-convex multi-period objective, with constants scaled by the concentrability of the initial distribution. It yields convergence rates for policy gradient methods to the global optimum.
--
--   **Formalization Note** The positivity $c>0$, $\mu\ge0$ of the constants is part of Definition 2 and is stated explicitly, so that the conclusion is not vacuous-false for an empty $\Theta$. The coefficient $\kappa$ is taken positive because Definition 2 requires a positive first constant; any $\kappa>0$ above $\kappa_\rho$ satisfies (13), so nothing is lost. The effective concentrability coefficient $\kappa_\rho$ is the smallest scalar satisfying (13); the statement is made for every $\kappa>0$ satisfying (13), which is the page's statement at $\kappa=\kappa_\rho$ whenever $0<\kappa_\rho<\infty$ (when $\kappa_\rho=\infty$ the page's bound is void). Condition 0 is used in the joint form that the proof of Lemma 6 (p. 39) needs: $(\bar\theta,\theta')\mapsto \mathcal B(\bar\theta\mid\eta_{\pi_{\theta'}},J_{\pi_\theta})$ is continuously differentiable on an open set containing $(\theta,\theta)$. Its two partial maps at $(\theta,\theta)$ are the two functions of the printed Condition 0, so it implies the printed condition; the printed condition alone does not give the total-derivative expansion of that proof. The standing assumptions of §2 are hypotheses: an optimal policy $\pi^*$ exists, Assumption 1 ($\eta_{\pi^*}\ll\rho$) and Assumption 2 (measurable selection; it also makes $TJ$ measurable, so the integrals of $TJ$ are genuine). State and action spaces are arbitrary measurable spaces and the cost $g$ and kernel $P$ are given (bounded, measurable) on all of $\mathcal S\times\mathcal A$; only their values on the feasible pairs enter $\Pi$, $T$ and $J^*$. The parameter space is $\mathbb R^d$ with the Euclidean inner product and norm.
-- source:
--   arXiv:1906.01786v3, Theorem 2, p. 16

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.GradDom

open MeasureTheory ProbabilityTheory

/-- Theorem 2, p. 16: if Conditions 0, 1 and 2.B hold (the latter with constants `c > 0`, `µ ≥ 0`),
then `ℓ` is `(κ_ρ/(1−γ) · c, κ_ρ/(1−γ) · µ)`-gradient dominated over `Θ`; stated for every `κ > 0`
satisfying (13), i.e. every finite positive upper bound on `κ_ρ`. -/
theorem loss_gradient_dominated {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar) (hA1 : PGLandscape.Closure.Assumption1 M πstar)
    (hA2 : PGLandscape.Closure.Assumption2 M)
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A)
    (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (c μ : ℝ) (hc : 0 < c) (hμ : 0 ≤ μ) (κ : ℝ) (hκ : 0 < κ) (hκb : PGLandscape.Closure.IsConcBound M Θ πθ πstar κ)
    (hC0 : PGLandscape.Closure.Condition0 M Θ πθ) (hC1 : PGLandscape.Closure.Condition1 M Θ πθ) (hC2B : PGLandscape.Closure.Condition2B M Θ πθ c μ) :
    PGLandscape.Closure.IsGradDominated (PGLandscape.Closure.lossParam M πθ) Θ (κ / (1 - M.γ) * c) (κ / (1 - M.γ) * μ) := by sorry

end PGLandscape.GradDom
