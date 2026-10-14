-- Prove2me | Theorems.Thm_StructEstMDP_FiniteTime_lemma_2
-- name    : StructEstMDP.FiniteTime.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:16.57024+00:00
-- url     : https://prove2.me/theorems/93f3bd97-1db1-4a20-9e6c-e007cb25a47a
-- title:
--   Lemma 2, p. 9 — gradients of L(θ) and L̂(θ; D): expert (or data) discounted ∇r minus soft-optimal-policy discounted ∇r
-- statement:
--   Let $(\mathcal S,\mathcal A,P,\rho,\gamma)$ be a finite MDP with initial distribution $\rho$ and discount $\gamma\in[0,1)$, and let the reward $r(s,a;\theta)$, $\theta\in\mathbb R^p$, satisfy Assumption 3. Let $\pi_\theta$ be the soft-optimal policy, $\pi^E$ an expert policy, $\mathcal D$ a nonempty dataset of trajectories, $L(\theta)$ the expert log-likelihood (4a) and $\widehat L(\theta;\mathcal D)$ the surrogate likelihood (9). Then $L$ and $\widehat L(\cdot;\mathcal D)$ are differentiable at every $\theta$, with
--
--   $$\nabla_\theta L(\theta)=\mathbb E_{\tau^E\sim\pi^E}\Big[\sum_{t=0}^\infty\gamma^t\nabla_\theta r(s_t,a_t;\theta)\Big]-\mathbb E_{\tau^A\sim\pi_\theta}\Big[\sum_{t=0}^\infty\gamma^t\nabla_\theta r(s_t,a_t;\theta)\Big],$$
--
--   $$\nabla_\theta \widehat L(\theta;\mathcal D)=\mathbb E_{\tau^E\sim\mathcal D}\Big[\sum_{t=0}^\infty\gamma^t\nabla_\theta r(s_t,a_t;\theta)\Big]-\mathbb E_{\tau^A\sim\pi_\theta}\Big[\sum_{t=0}^\infty\gamma^t\nabla_\theta r(s_t,a_t;\theta)\Big],$$
--
--   where trajectories of $\pi^E$ and $\pi_\theta$ start from $s_0\sim\rho$.
--
--   The formula (16b) is what makes $g_k=h(\theta_k;\tau^E_k)-h(\theta_k;\tau^A_k)$ a (biased) stochastic estimate of $\nabla_\theta\widehat L(\theta_k;\mathcal D)$, and it is the starting point of the smoothness bound (20b).
--
--   **Formalization Note** The conclusion is `HasGradientAt`, so differentiability is part of the claim. The page states Lemma 2 without hypotheses; the Lean adds Assumption 3 (differentiable rewards with bounded, Lipschitz gradients), which the proof uses, and the standing finite-MDP data.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, p. 9, Lemma 2, (16a)–(16b); proof §16, pp. 34–35

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace StructEstMDP.FiniteTime

/-- Lemma 2, p. 9: the gradients (16a) of the expert log-likelihood `L(θ)` and (16b) of the
surrogate likelihood `L̂(θ; D)`. -/
theorem lemma_2 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (ρ : S → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hρ : IsDist ρ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (Lr Lg : ℝ)
    (h3 : Assumption3 r Lr Lg)
    {m : ℕ} (D : Fin m → Traj S A) (hm : 0 < m)
    (πE : S → A → ℝ) (hπE : IsPolicy πE) (θ : EuclideanSpace ℝ (Fin p)) :
    HasGradientAt (Lexp P γ ρ r πE)
        (polMean P γ ρ πE (fun x => gradient (r x.1 x.2) θ) -
          polMean P γ ρ (optPolicy P γ r θ) (fun x => gradient (r x.1 x.2) θ)) θ ∧
      HasGradientAt (Lhat P γ ρ r D)
        (dataMean γ D (fun x => gradient (r x.1 x.2) θ) -
          polMean P γ ρ (optPolicy P γ r θ) (fun x => gradient (r x.1 x.2) θ)) θ := by sorry

end StructEstMDP.FiniteTime
