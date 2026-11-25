-- Prove2me | Theorems.Thm_WhenToTrustYourModel_mbpo_performance_bound
-- name    : WhenToTrustYourModel.mbpo_performance_bound
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T11:22:49.479609+00:00
-- url     : https://prove2.me/theorems/089f19f7-0f88-4cc7-8ed8-8590f3d167cf
-- title:
--   Theorem 4.1 (Theorem A.1): MBPO performance bound
-- statement:
--   Consider a discounted Markov decision process with finite state and action sets, true dynamics $p$, discount $\gamma\in(0,1)$, a reward with $|r(s,a)|\le r_{\max}$ and an initial distribution $\rho_0$. Let $\hat p$ be a learned model of the dynamics, $\pi_D$ the data-collecting policy and $\pi$ a new policy. Write $\eta[\pi]$ for the return of $\pi$ under $p$, $\hat\eta[\pi]$ for its return under $\hat p$, and $\pi_{D,t}$ for the state marginal at time $t$ of $\pi_D$ under $p$. Suppose
--
--   $$\max_t E_{s\sim\pi_{D,t},\,a\sim\pi_D(\cdot\mid s)}\big[D_{TV}\big(p(\cdot\mid s,a)\|\hat p(\cdot\mid s,a)\big)\big]\le\epsilon_m,\qquad \max_s D_{TV}\big(\pi_D(\cdot\mid s)\|\pi(\cdot\mid s)\big)\le\epsilon_\pi .$$
--
--   Then
--
--   $$\eta[\pi]\ge\hat\eta[\pi]-\left[\frac{2\gamma r_{\max}(\epsilon_m+2\epsilon_\pi)}{(1-\gamma)^2}+\frac{4r_{\max}\epsilon_\pi}{1-\gamma}\right].$$
--
--   Any improvement of the model return by more than the bracket $C(\epsilon_m,\epsilon_\pi)$ is therefore an improvement of the true return: this is the monotonic-improvement guarantee behind model-based policy optimization.
--
--   **Formalization Note** Theorem 4.1 measures the total variation of the joint law $p(s',r\mid s,a)$ of next state and reward, with a learned reward; the appendix version (Theorem A.1), which is the one proved, uses the dynamics $p(s'\mid s,a)$ and a known reward. The Lean statement is Theorem A.1. The paper does not say how actions are drawn in the model error; they are drawn from $\pi_D$, the policy whose data the model is trained on.
-- source:
--   Janner, Fu, Zhang and Levine, When to Trust Your Model: Model-Based Policy Optimization, arXiv:1906.08253v3 (NeurIPS 2019), Section 4.1, Theorem 4.1, eq. (1), p. 4; proof as Theorem A.1, Appendix A, p. 13

import Mathlib
import Definitions.Def_WhenToTrustYourModel_Basic

open Finset

namespace WhenToTrustYourModel

theorem mbpo_performance_bound {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (r : S → A → ℝ) (rmax : ℝ) (hr : ∀ s a, |r s a| ≤ rmax)
    (ρ₀ : S → ℝ) (hρ₀ : IsDist ρ₀)
    (π πD : S → A → ℝ) (hπ : IsPolicy π) (hπD : IsPolicy πD)
    (P Phat : S → A → S → ℝ) (hP : IsDynamics P) (hPhat : IsDynamics Phat)
    (εm επ : ℝ)
    (hm : ∀ t, expectedTV (stateDist ρ₀ (fun _ => πD) (fun _ => P) t) πD P Phat ≤ εm)
    (hdiv : ∀ s, tvDist (πD s) (π s) ≤ επ) :
    policyReturn γ r ρ₀ π Phat
        - (2 * γ * rmax * (εm + 2 * επ) / (1 - γ) ^ 2 + 4 * rmax * επ / (1 - γ)) ≤
      policyReturn γ r ρ₀ π P := by sorry

end WhenToTrustYourModel
