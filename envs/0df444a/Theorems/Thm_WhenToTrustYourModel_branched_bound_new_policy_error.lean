-- Prove2me | Theorems.Thm_WhenToTrustYourModel_branched_bound_new_policy_error
-- name    : WhenToTrustYourModel.branched_bound_new_policy_error
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:23:49.598961+00:00
-- url     : https://prove2.me/theorems/9c9fb225-0b7b-4979-be52-8d55b0032c03
-- title:
--   Theorem 4.3 (Theorem A.2): branched-rollout bound with model error under the new policy
-- statement:
--   In the setting of Theorem 4.1, fix a branch length $k\ge0$ and let $\eta^{\mathrm{branch}}[\pi]$ be the return of the $k$-branched rollout that runs $\pi$ under the model $\hat p$ for the $k$ branch steps and $\pi_D$ under the true dynamics $p$ otherwise. Write $\pi_t$ for the state marginal at time $t$ of $\pi$ under $p$. Suppose
--
--   $$\max_t E_{s\sim\pi_t,\,a\sim\pi(\cdot\mid s)}\big[D_{TV}\big(p(\cdot\mid s,a)\|\hat p(\cdot\mid s,a)\big)\big]\le\epsilon_{m'},\qquad \max_s D_{TV}\big(\pi_D(\cdot\mid s)\|\pi(\cdot\mid s)\big)\le\epsilon_\pi .$$
--
--   Then
--
--   $$\eta[\pi]\ge\eta^{\mathrm{branch}}[\pi]-2r_{\max}\left[\frac{\gamma^{k+1}\epsilon_\pi}{(1-\gamma)^2}+\frac{\gamma^k\epsilon_\pi}{1-\gamma}+\frac{k}{1-\gamma}\epsilon_{m'}\right].$$
--
--   With the model error measured under the new policy, the bound can favour a positive branch length $k$, which is the paper's argument for short model rollouts.
--
--   **Formalization Note** Theorem 4.3 in the main text writes the hypothesis with $s\sim\pi_{D,t}$ while calling $\epsilon_{m'}$ the model error under the updated policy; with $s\sim\pi_{D,t}$ the statement is false (a model exact on the states and actions of $\pi_D$ but wrong on an action only $\pi$ takes). The Lean statement follows Theorem A.2, which uses $s\sim\pi_t$, and draws actions from $\pi$. The branched rollout has its $k$ branch steps first, as in Lemma B.4.
-- source:
--   Janner, Fu, Zhang and Levine, When to Trust Your Model: Model-Based Policy Optimization, arXiv:1906.08253v3 (NeurIPS 2019), Section 4.3, Theorem 4.3, eq. (3), p. 5; stated and proved as Theorem A.2, Appendix A, p. 13

import Mathlib
import Definitions.Def_WhenToTrustYourModel_Basic

open Finset

namespace WhenToTrustYourModel

theorem branched_bound_new_policy_error {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (r : S → A → ℝ) (rmax : ℝ) (hr : ∀ s a, |r s a| ≤ rmax)
    (ρ₀ : S → ℝ) (hρ₀ : IsDist ρ₀) (k : ℕ)
    (π πD : S → A → ℝ) (hπ : IsPolicy π) (hπD : IsPolicy πD)
    (P Phat : S → A → S → ℝ) (hP : IsDynamics P) (hPhat : IsDynamics Phat)
    (εm' επ : ℝ)
    (hm : ∀ t, expectedTV (stateDist ρ₀ (fun _ => π) (fun _ => P) t) π P Phat ≤ εm')
    (hdiv : ∀ s, tvDist (πD s) (π s) ≤ επ) :
    branchedReturn γ r ρ₀ k π Phat πD P
        - 2 * rmax * (γ ^ (k + 1) * επ / (1 - γ) ^ 2 + γ ^ k * επ / (1 - γ)
          + k / (1 - γ) * εm') ≤
      policyReturn γ r ρ₀ π P := by sorry

end WhenToTrustYourModel
