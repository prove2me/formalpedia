-- Prove2me | Theorems.Thm_RandomHorizonPG_Asymp_rpg_asymptotic_convergence
-- name    : RandomHorizonPG.Asymp.rpg_asymptotic_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:45.46931+00:00
-- url     : https://prove2.me/theorems/0424ff3a-671c-43dd-af27-1ac0819c225f
-- title:
--   Theorem 4.2, p. 12 (proved form, p. 30) — RPG with Robbins–Monro stepsizes: ‖∇J(θ_k)‖ → 0 a.s. and every cluster point of θ_k is stationary
-- statement:
--   Let $(\mathcal S,\mathcal A,P,R,\gamma)$ be a finite discounted MDP with $\gamma\in(0,1)$, $s_0$ an initial state, and $\pi_\theta$, $\theta\in\mathbb R^d$, a parameterized policy satisfying Assumption 3.1 (bounded rewards, positive differentiable policies with bounded and Lipschitz score function). Let $J(\theta)=V_{\pi_\theta}(s_0)$. Let $(\theta_k)_{k\ge0}$ be the parameters produced by the random-horizon policy gradient algorithm (Algorithm 3),
--   $$
--   \theta_{k+1}=\theta_k+\frac{\alpha_k}{1-\gamma}\,\hat Q_{\pi_{\theta_k}}(s_{T_{k+1}},a_{T_{k+1}})\,\nabla\log\pi_{\theta_k}(a_{T_{k+1}}\mid s_{T_{k+1}}),
--   $$
--   with positive stepsizes satisfying the Robbins–Monro condition (Assumption 4.1)
--   $$
--   \sum_{k=0}^\infty\alpha_k=\infty,\qquad\sum_{k=0}^\infty\alpha_k^2<\infty.
--   $$
--   Then
--   1. almost surely, $\displaystyle\lim_{k\to\infty}\|\nabla J(\theta_k)\|=0$;
--   2. almost surely, every cluster point $\bar\theta$ of $(\theta_k)$ is a stationary point of $J$: $\nabla J(\bar\theta)=0$.
--
--   This is the asymptotic convergence guarantee for the basic RPG algorithm: with diminishing stepsizes, Monte Carlo policy gradient with random horizons approaches the set of stationary points of the nonconvex objective $J$.
--
--   **Formalization Note** The paper prints the conclusion as "$\lim_{k\to\infty}\theta_k\in\Theta^*$", the set of stationary points of $J$. Read literally this asserts that $\theta_k$ converges, which is false in general: for one state, two actions, the softmax policy, rewards $1$ and $0$, $J(\theta)=\sigma(\theta_1-\theta_2)/(1-\gamma)$ satisfies Assumption 3.1 and has no stationary point at all. The proof (App. A.3, p. 30) concludes "$\lim_{k\to\infty}\|\nabla J(\theta_k)\|=0$ a.s."; that is item 1, and item 2 is the true content of "$\theta_k\to\Theta^*$". Algorithm 3 is encoded by its explicit sampling law (see `Estimator`), not by an abstract unbiased oracle. $\alpha_k>0$ is added (the page says only "stepsize"; the proof divides by $\alpha_k$). Finite state and action spaces; the paper also covers compact continuous spaces.
-- source:
--   arXiv:1906.08383v3, Theorem 4.2, p. 12; Assumption 4.1, p. 12; App. A.3, pp. 26–30 (last sentence p. 30)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_RandomHorizonPG_Asymp_Setting
import Definitions.Def_RandomHorizonPG_Asymp_Estimator

namespace RandomHorizonPG.Asymp

open FoundationsML.ReinforcementLearning MeasureTheory Filter Topology

/-- arXiv:1906.08383v3, Theorem 4.2, p. 12, in the form its proof establishes (App. A.3, p. 30):
along a run of Algorithm 3 under Assumptions 3.1 and 4.1, `‖∇J(θ_k)‖ → 0` almost surely, and
almost surely every cluster point of `(θ_k)` is a stationary point of `J`. (The printed
"`lim θ_k ∈ Θ*`" asserts that `θ_k` converges, which fails when `J` has no stationary point.) -/
theorem rpg_asymptotic_convergence {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (R : S → A → ℝ) (γ UR LΘ BΘ : ℝ)
    (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) (s₀ : S)
    (hP : IsTransitionKernel P) (hγ : 0 < γ ∧ γ < 1) (hA : Assumption31 R UR π LΘ BΘ)
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (α : ℕ → ℝ) (hα : ∀ k, 0 < α k) (θ₀ : EuclideanSpace ℝ (Fin d))
    (θ g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hrun : IsRPGRun P R γ π s₀ α θ₀ μ ℱ θ g)
    (hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n, α k) atTop atTop)
    (hsq : Summable (fun k => α k ^ 2)) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => ‖gradient (objective P R γ π s₀) (θ k ω)‖) atTop (𝓝 0)) ∧
    (∀ᵐ ω ∂μ, ∀ θbar : EuclideanSpace ℝ (Fin d),
      MapClusterPt θbar atTop (fun k => θ k ω) → gradient (objective P R γ π s₀) θbar = 0) := by sorry

end RandomHorizonPG.Asymp
