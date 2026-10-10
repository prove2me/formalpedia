-- Prove2me | Theorems.Thm_QueueBandit_LateLower_theorem_3
-- name    : QueueBandit.LateLower.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:53.417584+00:00
-- url     : https://prove2.me/theorems/a9e4abc6-d73f-41aa-ab8e-13a7895391ce
-- title:
--   Theorem 3, p. 12 — every α-consistent policy has queue-regret ≥ (λ_min/8)D(μ)(1−α)(K−1)/t (average) infinitely often
-- statement:
--   Let $(\lambda,\mu)$ be a problem instance of a switch with $1\le U\le K$ queues and servers, $K\ge2$, with a unique optimal matching (Assumption 1) that is stable under it (Assumption 2: $\epsilon_u=\mu^*_u-\lambda_u>0$ for every $u$), and let $D(\mu)=\Delta/\mathrm{KL}(\mu_{\min},(\mu^*+1)/2)$ be given by display (2). Let the initial queue lengths have an arbitrary law, let $\alpha\in(0,1)$, and let the scheduling policy be $\alpha$-consistent. Then
--
--   1. for infinitely many $t$, $$\frac1U\sum_{u\in[U]}\Psi_u(t)\;\ge\;\Big(\frac{\lambda_{\min}}{8}D(\mu)(1-\alpha)(K-1)\Big)\frac1t;$$
--   2. for every queue $u$, for infinitely many $t$, $$\Psi_u(t)\;\ge\;\Big(\frac{\lambda_{\min}}{8}D(\mu)(1-\alpha)\max\{U-1,\,2(K-U)\}\Big)\frac1t.$$
--
--   No $\alpha$-consistent scheduling policy can therefore achieve queue-regret $o(1/t)$ in the late stage; the paper's Q-UCB attains the $1/t$ rate up to polylogarithmic factors.
--
--   **Formalization Note** "For infinitely many $t$" governs both parts and is `∃ᶠ t in atTop` over $t\in\mathbb N$; in part 2 the set of times may depend on $u$. Assumption 2 is the paper's standing assumption whenever queue-regret is evaluated (p. 8) and is a hypothesis here; Assumption 3 is not needed (p. 12): the law $\nu$ of $Q(0)$ is arbitrary. $K\ge2$ is added (for $K=1$ the policy and the genie coincide and both sides vanish). $D(\mu)=0$ when $\mu^*=1$. $\alpha$-consistency quantifies over every instance with entries in $[0,1]$ and Assumption 1, not only the given one.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 12, Theorem 3; proof §9.1, pp. 41–42

import Mathlib
import Definitions.Def_QueueBandit_LateLower_Instance
import Definitions.Def_QueueBandit_LateLower_Dynamics

open MeasureTheory Finset Filter

namespace QueueBandit.LateLower

/-- Theorem 3 (p. 12). For every instance with a unique optimal matching (Assumption 1) that is
stable under the optimal matching (Assumption 2, ε_u = μ*_u − λ_u > 0), every initial law of
the queue lengths, and every α-consistent policy, for infinitely many t
(a) the average queue-regret is at least (λ_min/8) D(μ)(1 − α)(K − 1)/t, and
(b) each queue's regret is at least (λ_min/8) D(μ)(1 − α) max{U − 1, 2(K − U)}/t. -/
theorem theorem_3 {U K : ℕ} (hU : 0 < U) (hUK : U ≤ K) (hK : 2 ≤ K)
    (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hinst : IsInstance lam mu kstar) (hA2 : ∀ u, lam u < mu u (kstar u))
    (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (π : Policy U K) (hπ : IsAlphaConsistent π α) :
    (∃ᶠ t : ℕ in atTop,
      lamMin lam / 8 * D mu kstar * (1 - α) * ((K : ℝ) - 1) * (1 / (t : ℝ)) ≤
        (1 / (U : ℝ)) * ∑ u, queueRegret lam mu kstar ν π u t) ∧
    ∀ u : Fin U, ∃ᶠ t : ℕ in atTop,
      lamMin lam / 8 * D mu kstar * (1 - α) * max ((U : ℝ) - 1) (2 * ((K : ℝ) - U)) *
          (1 / (t : ℝ)) ≤
        queueRegret lam mu kstar ν π u t := by sorry

end QueueBandit.LateLower
