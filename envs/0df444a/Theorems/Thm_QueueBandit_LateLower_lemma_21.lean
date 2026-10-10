-- Prove2me | Theorems.Thm_QueueBandit_LateLower_lemma_21
-- name    : QueueBandit.LateLower.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:42.329019+00:00
-- url     : https://prove2.me/theorems/c2cc6bb9-6dce-43cc-ac00-8c650e34d2e2
-- title:
--   Lemma 21, p. 41 — one-slot bound Ψ_u(t) ≥ λ_u Σ_{k≠k*_u} Δ_uk P[κ_u(t) = k] for every policy
-- statement:
--   Let $(\lambda,\mu)$ be an instance of a switch with $U\le K$ satisfying Assumptions 1 and 2 ($\lambda_u<\mu^*_u$ for every $u$), with gaps $\Delta_{uk}=\mu^*_u-\mu_{uk}$. For every scheduling policy, every law of the initial queue lengths, every queue $u$ and every slot $t\ge1$,
--   $$\Psi_u(t)\;\ge\;\lambda_u\sum_{k\neq k^*_u}\Delta_{uk}\,\mathbb P\big[\kappa_u(t)=k\big].$$
--
--   The queue-regret in a single slot is thus bounded below by the expected service-rate loss of that slot, weighted by the arrival probability. Summed over slots and combined with Corollary 20, it turns a lower bound on suboptimal schedules into a lower bound on cumulative queue-regret.
--
--   **Formalization Note** The statement is about the original model with independent services across links; the paper's proof passes to a coupled service process with the same marginal laws, which is a proof device and does not appear here. Assumption 2 is the paper's standing assumption whenever queue-regret is evaluated (p. 8). Time is 1-based ($t\ge1$). $\Psi_u(t)$ is the integral of $Q_u(t)-Q^*_u(t)$, which is bounded by $t$ in absolute value because the two systems share initial state, arrivals and offered services.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 41, Lemma 21; proof p. 41 (coupling of §8.1, pp. 22–23)

import Mathlib
import Definitions.Def_QueueBandit_LateLower_Instance
import Definitions.Def_QueueBandit_LateLower_Dynamics

open MeasureTheory Finset Filter

namespace QueueBandit.LateLower

/-- Lemma 21 (p. 41). For any instance satisfying Assumptions 1 and 2 (the standing setting in
which queue-regret is evaluated, p. 8), any scheduling policy, any initial law of the queue
lengths, every queue u and every slot t ≥ 1, Ψ_u(t) ≥ λ_u Σ_{k ≠ k*_u} Δ_uk P[κ_u(t) = k]. -/
theorem lemma_21 {U K : ℕ} (hUK : U ≤ K)
    (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hinst : IsInstance lam mu kstar) (hA2 : ∀ u, lam u < mu u (kstar u))
    (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν]
    (π : Policy U K) (u : Fin U) (t : ℕ) (ht : 1 ≤ t) :
    lam u * ∑ k ∈ univ.erase (kstar u),
        gap mu kstar u k * (sysMeasure (K := K) ν).real {x | sched π mu x.2 t u = k} ≤
      queueRegret lam mu kstar ν π u t := by sorry

end QueueBandit.LateLower
