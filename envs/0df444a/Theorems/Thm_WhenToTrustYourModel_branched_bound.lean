-- Prove2me | Theorems.Thm_WhenToTrustYourModel_branched_bound
-- name    : WhenToTrustYourModel.branched_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:24:21.480418+00:00
-- url     : https://prove2.me/theorems/ab8a721d-7ba4-4c80-ac4d-e718544355f7
-- title:
--   Theorem 4.2 (Theorem A.3): branched-rollout bound
-- statement:
--   In the setting of Theorem 4.1, fix a branch length $k\ge0$ and let $\eta^{\mathrm{branch}}[\pi]$ be the return of the $k$-branched rollout that runs $\pi$ under the model $\hat p$ for the $k$ branch steps and $\pi_D$ under the true dynamics $p$ otherwise. Suppose, with $\pi_{D,t}$ the state marginal at time $t$ of $\pi_D$ under $p$,
--
--   $$\max_t E_{s\sim\pi_{D,t},\,a\sim\pi_D(\cdot\mid s)}\big[D_{TV}\big(p(\cdot\mid s,a)\|\hat p(\cdot\mid s,a)\big)\big]\le\epsilon_m,\qquad \max_s D_{TV}\big(\pi_D(\cdot\mid s)\|\pi(\cdot\mid s)\big)\le\epsilon_\pi .$$
--
--   Then
--
--   $$\eta[\pi]\ge\eta^{\mathrm{branch}}[\pi]-2r_{\max}\left[\frac{\gamma^{k+1}\epsilon_\pi}{(1-\gamma)^2}+\frac{\gamma^k+2}{1-\gamma}\epsilon_\pi+\frac{k}{1-\gamma}(\epsilon_m+2\epsilon_\pi)\right].$$
--
--   This bounds the true return of the new policy by the return of short model rollouts branched from the data distribution, in terms of the model error on the data-collecting policy's own distribution.
--
--   **Formalization Note** The branched rollout has its $k$ branch steps first, as in Lemma B.4. Actions in the model error are drawn from $\pi_D$.
-- source:
--   Janner, Fu, Zhang and Levine, When to Trust Your Model: Model-Based Policy Optimization, arXiv:1906.08253v3 (NeurIPS 2019), Section 4.2, Theorem 4.2, eq. (2), p. 4; stated and proved as Theorem A.3, Appendix A, p. 14

import Mathlib
import Definitions.Def_WhenToTrustYourModel_Basic

open Finset

namespace WhenToTrustYourModel

theorem branched_bound {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (r : S → A → ℝ) (rmax : ℝ) (hr : ∀ s a, |r s a| ≤ rmax)
    (ρ₀ : S → ℝ) (hρ₀ : IsDist ρ₀) (k : ℕ)
    (π πD : S → A → ℝ) (hπ : IsPolicy π) (hπD : IsPolicy πD)
    (P Phat : S → A → S → ℝ) (hP : IsDynamics P) (hPhat : IsDynamics Phat)
    (εm επ : ℝ)
    (hm : ∀ t, expectedTV (stateDist ρ₀ (fun _ => πD) (fun _ => P) t) πD P Phat ≤ εm)
    (hdiv : ∀ s, tvDist (πD s) (π s) ≤ επ) :
    branchedReturn γ r ρ₀ k π Phat πD P
        - 2 * rmax * (γ ^ (k + 1) * επ / (1 - γ) ^ 2 + (γ ^ k + 2) / (1 - γ) * επ
          + k / (1 - γ) * (εm + 2 * επ)) ≤
      policyReturn γ r ρ₀ π P := by sorry

end WhenToTrustYourModel
