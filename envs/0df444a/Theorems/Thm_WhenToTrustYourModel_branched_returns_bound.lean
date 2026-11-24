-- Prove2me | Theorems.Thm_WhenToTrustYourModel_branched_returns_bound
-- name    : WhenToTrustYourModel.branched_returns_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:23:13.957488+00:00
-- url     : https://prove2.me/theorems/dc86f8e2-a86e-46e6-b0e9-c18dddf93b8c
-- title:
--   Lemma B.4 (as proved): returns bound, branched rollout
-- statement:
--   Consider a discounted Markov decision process with finite state and action sets, discount $\gamma\in(0,1)$, a reward with $|r(s,a)|\le r_{\max}$ and an initial distribution $\rho_0$. Fix a branch length $k\ge0$. For $i=1,2$, process $i$ starts from $\rho_0$, uses the post-branch policy $\pi_i^{\mathrm{post}}$ and dynamics $p_i^{\mathrm{post}}$ at the $k$ branch steps $t<k$, and the pre-branch policy $\pi_i^{\mathrm{pre}}$ and dynamics $p_i^{\mathrm{pre}}$ at the steps $t\ge k$; $\eta_i$ is its return and $p_1^t$ is the state marginal of process 1. Suppose
--
--   1. $E_{s\sim p_1^t,\,a\sim\pi_1^{\mathrm{pre}}}\big[D_{TV}(p_1^{\mathrm{pre}}(\cdot\mid s,a)\|p_2^{\mathrm{pre}}(\cdot\mid s,a))\big]\le\epsilon_m^{\mathrm{pre}}$ for every $t\ge k$;
--   2. $E_{s\sim p_1^t,\,a\sim\pi_1^{\mathrm{post}}}\big[D_{TV}(p_1^{\mathrm{post}}(\cdot\mid s,a)\|p_2^{\mathrm{post}}(\cdot\mid s,a))\big]\le\epsilon_m^{\mathrm{post}}$ for every $t<k$;
--   3. $\max_s D_{TV}(\pi_1^{\mathrm{pre}}(\cdot\mid s)\|\pi_2^{\mathrm{pre}}(\cdot\mid s))\le\epsilon_\pi^{\mathrm{pre}}$ and $\max_s D_{TV}(\pi_1^{\mathrm{post}}(\cdot\mid s)\|\pi_2^{\mathrm{post}}(\cdot\mid s))\le\epsilon_\pi^{\mathrm{post}}$.
--
--   Then
--
--   $$|\eta_1-\eta_2|\le2r_{\max}\left[\frac{\gamma^{k+1}}{(1-\gamma)^2}(\epsilon_m^{\mathrm{pre}}+\epsilon_\pi^{\mathrm{pre}})+\frac{k}{1-\gamma}(\epsilon_m^{\mathrm{post}}+\epsilon_\pi^{\mathrm{post}})+\frac{\gamma^k}{1-\gamma}\epsilon_\pi^{\mathrm{pre}}+\frac{1}{1-\gamma}\epsilon_\pi^{\mathrm{post}}\right].$$
--
--   This is the returns bound from which Theorems 4.2 and 4.3 are assembled.
--
--   **Formalization Note** The paper does not define the branched rollout formally. Its proof bounds the state-action marginals at the times $t\le k$ by the post-branch errors alone and at the times $t\ge k$ by $(t-k)$ pre-branch errors plus $k$ post-branch errors, so the branch segment is the first $k$ time steps; the Lean statement uses that ordering. If instead the pre-branch segment comes first, as the text of Section 4.2 suggests, the statement is false: with one state, rewards $\pm1$, $\gamma=1/2$, $k=10$ and pre-branch policies at total variation $1$ used only at times $t=0$ and $t\ge11$, the returns differ by about $2.002$ while the bound is $0.0078$. The paper writes the model error as an expected KL divergence of $p_i(s',a\mid s)$; as in Lemma B.3, the proof uses the total variation of the dynamics. The pre-branch and post-branch model errors are required at the pre-branch and post-branch times respectively.
-- source:
--   Janner, Fu, Zhang and Levine, When to Trust Your Model: Model-Based Policy Optimization, arXiv:1906.08253v3 (NeurIPS 2019), Appendix B, Lemma B.4, p. 17

import Mathlib
import Definitions.Def_WhenToTrustYourModel_Basic

open Finset

namespace WhenToTrustYourModel

theorem branched_returns_bound {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (r : S → A → ℝ) (rmax : ℝ) (hr : ∀ s a, |r s a| ≤ rmax)
    (ρ₀ : S → ℝ) (hρ₀ : IsDist ρ₀) (k : ℕ)
    (π₁pre π₂pre π₁post π₂post : S → A → ℝ)
    (hπ₁pre : IsPolicy π₁pre) (hπ₂pre : IsPolicy π₂pre)
    (hπ₁post : IsPolicy π₁post) (hπ₂post : IsPolicy π₂post)
    (P₁pre P₂pre P₁post P₂post : S → A → S → ℝ)
    (hP₁pre : IsDynamics P₁pre) (hP₂pre : IsDynamics P₂pre)
    (hP₁post : IsDynamics P₁post) (hP₂post : IsDynamics P₂post)
    (εmpre εmpost επpre επpost : ℝ)
    (hmpre : ∀ t, k ≤ t →
      expectedTV (stateDist ρ₀ (phase k π₁post π₁pre) (phase k P₁post P₁pre) t)
        π₁pre P₁pre P₂pre ≤ εmpre)
    (hmpost : ∀ t, t < k →
      expectedTV (stateDist ρ₀ (phase k π₁post π₁pre) (phase k P₁post P₁pre) t)
        π₁post P₁post P₂post ≤ εmpost)
    (hπpre : ∀ s, tvDist (π₁pre s) (π₂pre s) ≤ επpre)
    (hπpost : ∀ s, tvDist (π₁post s) (π₂post s) ≤ επpost) :
    |branchedReturn γ r ρ₀ k π₁post P₁post π₁pre P₁pre -
        branchedReturn γ r ρ₀ k π₂post P₂post π₂pre P₂pre| ≤
      2 * rmax * (γ ^ (k + 1) / (1 - γ) ^ 2 * (εmpre + επpre) + k / (1 - γ) * (εmpost + επpost)
        + γ ^ k / (1 - γ) * επpre + 1 / (1 - γ) * επpost) := by sorry

end WhenToTrustYourModel
