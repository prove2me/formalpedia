-- Prove2me | Theorems.Thm_PGLandscape_GradDom_closure_gap_bound
-- name    : PGLandscape.GradDom.closure_gap_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:21.597606+00:00
-- url     : https://prove2.me/theorems/7d1e1290-129f-4fe7-8a6c-76dacc7158df
-- title:
--   §5.3, proof of Theorem 2, first display, p. 16 — under closure, ℓ(π_θ) − ℓ(π*) ≤ κ_ρ/(1−γ) (B(θ | η, J) − min_{θ′∈Θ} B(θ′ | η, J))
-- statement:
--   Let $\Pi_\Theta$ be a parameterized policy class satisfying Condition 1 (closure under policy improvement), let $\pi^*$ be an optimal policy, and let $\kappa>0$ satisfy (13). Fix $\theta\in\Theta$ and write $\eta=\eta_{\pi_\theta}$, $J=J_{\pi_\theta}$. Then the minimum of $\theta'\mapsto\mathcal B(\theta'\mid\eta,J)$ over $\Theta$ is attained at some $\theta^+\in\Theta$, and
--   $$\ell(\pi_\theta)-\ell(\pi^*)\ \le\ \frac{\kappa}{1-\gamma}\Big(\mathcal B(\theta\mid\eta,J)-\min_{\theta'\in\Theta}\mathcal B(\theta'\mid\eta,J)\Big).$$
--
--   The optimality gap of any policy in the class is controlled by the improvement a single weighted policy iteration step could achieve inside the class. This is the first of the two steps of the proof of Theorem 2.
--
--   **Formalization Note** The page's $\min_{\pi\in\Pi}\ell(\pi)$ is $\ell(\pi^*)$, and its $\min_{\theta'\in\Theta}\mathcal B(\theta'\mid\eta,J)$ is written as the value at an explicitly produced minimizer $\theta^+$. The effective concentrability coefficient $\kappa_\rho$ is the smallest scalar satisfying (13); the statement is made for every $\kappa>0$ satisfying (13), which is the page's statement at $\kappa=\kappa_\rho$ whenever $0<\kappa_\rho<\infty$ (when $\kappa_\rho=\infty$ the page's bound is void). The standing assumptions of §2 are hypotheses: an optimal policy $\pi^*$ exists, Assumption 1 ($\eta_{\pi^*}\ll\rho$) and Assumption 2 (measurable selection; it also makes $TJ$ measurable, so the integrals of $TJ$ are genuine). State and action spaces are arbitrary measurable spaces and the cost $g$ and kernel $P$ are given (bounded, measurable) on all of $\mathcal S\times\mathcal A$; only their values on the feasible pairs enter $\Pi$, $T$ and $J^*$. The parameter space is $\mathbb R^d$ with the Euclidean inner product and norm.
-- source:
--   arXiv:1906.01786v3, §5.3, proof of Theorem 2, first display, p. 16

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.GradDom

open MeasureTheory ProbabilityTheory

/-- §5.3, proof of Theorem 2, first display, p. 16: under closure (Condition 1), for every `θ ∈ Θ`
the minimum of `θ' ↦ B(θ' | η_{π_θ}, J_{π_θ})` over `Θ` is attained at some `θ⁺ ∈ Θ`, and
`ℓ(π_θ) − ℓ(π*) ≤ κ/(1−γ) (B(θ | η_{π_θ}, J_{π_θ}) − B(θ⁺ | η_{π_θ}, J_{π_θ}))` for every `κ > 0`
satisfying (13). -/
theorem closure_gap_bound {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar) (hA1 : PGLandscape.Closure.Assumption1 M πstar)
    (hA2 : PGLandscape.Closure.Assumption2 M)
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A)
    (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ) (hC1 : PGLandscape.Closure.Condition1 M Θ πθ)
    (κ : ℝ) (hκ : 0 < κ) (hκb : PGLandscape.Closure.IsConcBound M Θ πθ πstar κ)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ Θ) :
    ∃ θplus ∈ Θ, (∀ θ' ∈ Θ, PGLandscape.Closure.piObjective M πθ θ θplus ≤ PGLandscape.Closure.piObjective M πθ θ θ') ∧
      PGLandscape.Closure.loss M (πθ θ) - PGLandscape.Closure.loss M πstar ≤
        κ / (1 - M.γ) * (PGLandscape.Closure.piObjective M πθ θ θ - PGLandscape.Closure.piObjective M πθ θ θplus) := by sorry

end PGLandscape.GradDom
