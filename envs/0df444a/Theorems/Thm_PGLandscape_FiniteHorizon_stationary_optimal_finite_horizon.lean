-- Prove2me | Theorems.Thm_PGLandscape_FiniteHorizon_stationary_optimal_finite_horizon
-- name    : PGLandscape.FiniteHorizon.stationary_optimal_finite_horizon
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:45.161708+00:00
-- url     : https://prove2.me/theorems/62d0fea3-fe4e-435c-9595-d0570ae8cc8c
-- title:
--   Theorem 3, p. 17 — under Conditions 3, 4 (with 0 and Assumption 3), if Π_Θ contains an optimal policy, every stationary point θ of ℓ satisfies ℓ(π_θ) = ℓ(π*)
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process with an optimal policy $\pi^*$, satisfying Assumption 1 ($\eta_{\pi^*}\ll\rho$) and Assumption 2 (measurable selection). Let $\Pi_\Theta=\{\pi_\theta:\theta\in\Theta\}$ be a parameterized policy class over a convex set $\Theta\subseteq\mathbb R^d$, with $\ell(\theta)=\ell(\pi_\theta)=(1-\gamma)\int J_{\pi_\theta}\,d\rho$. Suppose
--   1. Condition 3: the problem has finite horizon $H$ — the states split into stages $\mathcal S_1,\dots,\mathcal S_H,\mathcal S_{H+1}=\{\tau\}$ with stage $h\le H$ leading to stage $h+1$ under every feasible action and $\tau$ a costless absorbing state — and the policy class is non-stationary: $\Theta=\Theta_1\times\cdots\times\Theta_H$ and on $\mathcal S_h$ the action $\pi_\theta(s)$ depends only on $\theta_h$;
--   2. Condition 4: for every $\eta\in\{\eta_\pi:\pi\in\Pi_\Theta\}$, $\min_{\theta\in\Theta}\mathcal B(\theta\mid\eta,J^*)$ has no suboptimal stationary points;
--   3. Condition 0 (differentiability) and Assumption 3 ($\eta_\pi\ll\rho$ for every $\pi\in\Pi_\Theta$);
--   4. $\Pi_\Theta$ contains an optimal policy: $\pi_{\theta^*}$ is optimal among all feasible policies for some $\theta^*\in\Theta$.
--
--   Then every stationary point $\theta$ of $\ell$ on $\Theta$ satisfies
--   $$\ell(\pi_\theta)=\ell(\pi^*).$$
--
--   For finite-horizon problems with non-stationary policies it suffices that the class contains an optimal policy; closure under policy improvement (Theorem 1) is not needed, and the single-period condition is imposed only on the Bellman objective of the optimal cost-to-go $J^*$.
--
--   **Formalization Note** The page's sentence names Conditions 3 and 4 only. Assumption 3 is announced on p. 17 as required ("for our argument to work only with Condition 4, we do require …"; "Assumption 3 is crucial for our proof") and used in the proof; Condition 0 is needed for Lemma 6, which the proof invokes, and for "stationary point of $\ell$" to involve a gradient. Both are hypotheses. Condition 0 is the joint form of the definition file. Condition 4 includes differentiability of $\theta\mapsto\mathcal B(\theta\mid\eta,J^*)$ at the points of $\Theta$, the premise of Definition 1. Assumptions 1 and 2 are standing assumptions of §2. "Contains an optimal policy" means optimal among all feasible measurable stationary policies, not merely among $\Pi_\Theta$. A stationary point includes differentiability of $\ell$ at $\theta$. The discount $\gamma\in(0,1)$ is kept. The Bellman operators include the factor $\gamma$ omitted in the printed (3)–(4).
-- source:
--   arXiv:1906.01786v3, Theorem 3, §5.4, p. 17 (proof App. D.2, pp. 40–42)

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions
import Definitions.Def_PGLandscape_FiniteHorizon_Stages

namespace PGLandscape.FiniteHorizon

open MeasureTheory ProbabilityTheory

/-- Theorem 3, arXiv:1906.01786v3, p. 17 (proof pp. 40–42): suppose Conditions 3 and 4 hold (and,
as the proof requires, Condition 0 and Assumption 3). If the parameterized policy class `Π_Θ`
contains an optimal policy, then every stationary point `θ` of `ℓ : Θ → ℝ` satisfies
`ℓ(π_θ) = ℓ(π*)`. -/
theorem stationary_optimal_finite_horizon {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar)
    (hA1 : PGLandscape.Closure.Assumption1 M πstar) (hA2 : PGLandscape.Closure.Assumption2 M)
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) (hΘ : PGLandscape.Closure.IsPolicyClass M Θ πθ)
    (H : ℕ) (stage : S → ℕ) (τ : S) (blk : Fin d → ℕ)
    (hC0 : PGLandscape.Closure.Condition0 M Θ πθ) (hC3 : Condition3 M H stage τ blk Θ πθ)
    (hC4 : Condition4 M Θ πθ πstar) (hA3 : Assumption3 M Θ πθ)
    (hcontains : ∃ θstar ∈ Θ, PGLandscape.Closure.IsOptimal M (πθ θstar)) :
    ∀ θ : EuclideanSpace ℝ (Fin d), PGLandscape.Closure.IsStationary (PGLandscape.Closure.lossParam M πθ) Θ θ →
      PGLandscape.Closure.loss M (πθ θ) = PGLandscape.Closure.loss M πstar := by sorry

end PGLandscape.FiniteHorizon
