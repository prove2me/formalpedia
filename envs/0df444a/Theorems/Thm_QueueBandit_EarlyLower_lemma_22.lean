-- Prove2me | Theorems.Thm_QueueBandit_EarlyLower_lemma_22
-- name    : QueueBandit.EarlyLower.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:18.170545+00:00
-- url     : https://prove2.me/theorems/bc69c8a7-5bab-48c4-8b89-7da688a5f27a
-- title:
--   Lemma 22, p. 42 — Ψ_u(t) ≥ Σ_{k≠k*_u} Δ_uk E[T_uk(t+1)] − ε_u t
-- statement:
--   Consider the $U\times K$ switch ($U\le K$, $K\ge2$) with arrival rates $\lambda_u\in[0,1]$, service probabilities $\mu_{uk}\in[0,1]$, and a unique optimal matching $k^*$ (Assumption 1). Assume every queue is stable under the optimal matching, $\epsilon_u=\mu^*_u-\lambda_u>0$ (Assumption 2), and that the initial queue vector $Q(0)$ has the stationary law $\pi_{(\lambda,\mu^*)}$ of the genie queues (Assumption 3). Then for **any** scheduling policy, any queue $u$ and any time $t\ge0$,
--
--   $$\Psi_u(t)\;\ge\;\sum_{k\neq k^*_u}\Delta_{uk}\,\mathbb E[T_{uk}(t+1)]-\epsilon_u t .$$
--
--   The lemma converts the number of sub-optimal schedules into queue-regret, up to a load term $\epsilon_u t$ that is small in heavy traffic. It is the queueing half of Theorem 8.
--
--   **Formalization Note.** The policy need not be consistent. The initial law is the product of the geometric laws $(1-\rho_u)\rho_u^n$, $\rho_u=\lambda_u(1-\mu^*_u)/((1-\lambda_u)\mu^*_u)$, which is the stationary law of the genie recursion. The genie queue shares the initial state, arrivals and potential services of the policy's queue. $K\ge2$ is a standing assumption of the mission.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 42, Lemma 22; proof p. 43; Assumptions 1–3, pp. 7–8

import Mathlib
import Definitions.Def_QueueBandit_EarlyLower_Model
import Definitions.Def_QueueBandit_LateLower_Dynamics

namespace QueueBandit.EarlyLower

/-- Lemma 22 (arXiv:1604.06377v4, p. 42). For an instance with a unique optimal matching, stable
under the optimal matching (Assumption 2), started from the stationary law of `Q*`
(Assumption 3), for any policy, any queue `u` and any `t`,
`Ψ_u(t) ≥ Σ_{k ≠ k*_u} Δ_{uk} E[T_{uk}(t+1)] − ε_u t`. -/
theorem lemma_22 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K)
    (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hlam : ∀ u, 0 ≤ lam u ∧ lam u ≤ 1) (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1)
    (hA1 : QueueBandit.LateLower.Assumption1 mu kstar) (hA2 : ∀ u, 0 < eps lam mu kstar u)
    (π : QueueBandit.LateLower.Policy U K) (u : Fin U) (t : ℕ) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
        QueueBandit.LateLower.gap mu kstar u k * QueueBandit.LateLower.expCount π mu u k t) -
        eps lam mu kstar u * t ≤
      QueueBandit.LateLower.queueRegret lam mu kstar (initLaw lam mu kstar) π u t := by sorry

end QueueBandit.EarlyLower
