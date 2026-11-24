-- Prove2me | Theorems.Thm_WhenToTrustYourModel_returns_bound
-- name    : WhenToTrustYourModel.returns_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:22:20.01072+00:00
-- url     : https://prove2.me/theorems/69ca6d2d-c827-4ca9-91bb-6b8ef332066c
-- title:
--   Lemma B.3 (as proved): returns bound
-- statement:
--   Consider a discounted Markov decision process with finite state and action sets, discount $\gamma\in(0,1)$, a reward with $|r(s,a)|\le r_{\max}$ and an initial distribution $\rho_0$. Let $\eta_1$ be the return of policy $\pi_1$ under dynamics $p_1$, and $\eta_2$ the return of policy $\pi_2$ under dynamics $p_2$, both started from $\rho_0$, and let $p_1^t$ be the state marginal at time $t$ of the first process. Suppose
--
--   $$\max_t E_{s\sim p_1^t,\,a\sim\pi_1(\cdot\mid s)}\big[D_{TV}\big(p_1(\cdot\mid s,a)\|p_2(\cdot\mid s,a)\big)\big]\le\epsilon_m,\qquad \max_s D_{TV}\big(\pi_1(\cdot\mid s)\|\pi_2(\cdot\mid s)\big)\le\epsilon_\pi .$$
--
--   Then
--
--   $$|\eta_1-\eta_2|\le\frac{2r_{\max}\gamma(\epsilon_\pi+\epsilon_m)}{(1-\gamma)^2}+\frac{2r_{\max}\epsilon_\pi}{1-\gamma}.$$
--
--   This is the basic simulation bound from which Theorem 4.1 is assembled.
--
--   **Formalization Note** The paper's statement assumes a bound on an expected KL divergence of $p_i(s',a\mid s)$, but the proof uses the total variation of the dynamics, through Lemma B.2 with $\delta=\epsilon_m+\epsilon_\pi$, and that is how the lemma is applied in Theorem A.1. With the KL hypothesis the statement is false. The Lean statement uses the total variation of the dynamics, averaged over $s\sim p_1^t$ and $a\sim\pi_1(\cdot\mid s)$, as proved. The paper's constant $R$ is $r_{\max}$.
-- source:
--   Janner, Fu, Zhang and Levine, When to Trust Your Model: Model-Based Policy Optimization, arXiv:1906.08253v3 (NeurIPS 2019), Appendix B, Lemma B.3, p. 16

import Mathlib
import Definitions.Def_WhenToTrustYourModel_Basic

open Finset

namespace WhenToTrustYourModel

theorem returns_bound {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (r : S → A → ℝ) (rmax : ℝ) (hr : ∀ s a, |r s a| ≤ rmax)
    (ρ₀ : S → ℝ) (hρ₀ : IsDist ρ₀)
    (π₁ π₂ : S → A → ℝ) (hπ₁ : IsPolicy π₁) (hπ₂ : IsPolicy π₂)
    (P₁ P₂ : S → A → S → ℝ) (hP₁ : IsDynamics P₁) (hP₂ : IsDynamics P₂)
    (εm επ : ℝ)
    (hm : ∀ t, expectedTV (stateDist ρ₀ (fun _ => π₁) (fun _ => P₁) t) π₁ P₁ P₂ ≤ εm)
    (hπ : ∀ s, tvDist (π₁ s) (π₂ s) ≤ επ) :
    |policyReturn γ r ρ₀ π₁ P₁ - policyReturn γ r ρ₀ π₂ P₂| ≤
      2 * rmax * γ * (επ + εm) / (1 - γ) ^ 2 + 2 * rmax * επ / (1 - γ) := by sorry

end WhenToTrustYourModel
