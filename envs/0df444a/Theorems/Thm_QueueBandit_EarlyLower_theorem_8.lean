-- Prove2me | Theorems.Thm_QueueBandit_EarlyLower_theorem_8
-- name    : QueueBandit.EarlyLower.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:25.22484+00:00
-- url     : https://prove2.me/theorems/8deebf23-f8e4-46c5-b6bf-8fb7c5d8ff2a
-- title:
--   Theorem 8, p. 18 — in heavy traffic every α-consistent policy has queue-regret ≥ (D(μ)/4)(K−1) log t/log log t on [max{C₁K^γ, τ}, (K−1)D(μ)/(4ε̄)]
-- statement:
--   Consider the $U\times K$ switch with $1\le U\le K$, $K\ge2$, service probabilities $\mu_{uk}\in[0,1]$ and a unique optimal matching $k^*$. Let $\alpha\in(0,1)$, fix an $\alpha$-consistent scheduling policy and let $\gamma>1/(1-\alpha)$. Then there exist constants $\tau>e$ and $C_1>0$, which do not depend on the arrival rates, with the following property. Let $\lambda\in[0,1]^U$ be any arrival vector such that every $\epsilon_u=\mu^*_u-\lambda_u>0$, and let the system start from the stationary law of the genie queues (Assumption 3). Put
--
--   $$T_0=\max\{C_1K^{\gamma},\tau\},\qquad \eta=\frac{(K-1)D(\mu)}{2T_0},\qquad \bar\epsilon=\frac1U\sum_{u}\epsilon_u .$$
--
--   1. If $\bar\epsilon<\eta/2$, then for every integer $t\in\big[T_0,\,(K-1)\frac{D(\mu)}{4\bar\epsilon}\big]$,
--   $$\frac1U\sum_{u}\Psi_u(t)\ \ge\ \frac{D(\mu)}{4}(K-1)\frac{\log t}{\log\log t}.$$
--   2. For every queue $u$ with $\epsilon_u<\eta$ and every integer $t\in\big[T_0,\,(K-1)\frac{D(\mu)}{2\epsilon_u}\big]$,
--   $$\Psi_u(t)\ \ge\ \frac{D(\mu)}{4}\max\{U-1,\,2(K-U)\}\frac{\log t}{\log\log t}.$$
--
--   In heavy traffic ($\epsilon\to0$) the right end of the window grows like $1/\epsilon$ while the left end stays fixed. On that window the queue-regret of any consistent policy grows like $\log t/\log\log t$, as in a classical bandit's regret, before the late-stage decay of order $1/t$ of Theorem 3 sets in.
--
--   **Formalization Note.** The paper says that $\tau$ and $C_1$ are "independent of $(\lambda,\mu)$". Its proof (p. 43) takes them from Corollary 20, whose constants come from the consistency constants of $\mu$ and of the perturbed instances of Lemma 19. Here they are chosen after $\mu$, $\alpha$, $\gamma$, $K$, $U$ and the policy, but **before** the arrival vector $\lambda$. Independence of $\lambda$ holds because the policy never observes arrivals. Choosing the constants after $\lambda$ would make the theorem vacuous, since a large $C_1$ makes $\eta/2<\bar\epsilon$. The constant $\tau$ is required to exceed $e$, so $\log\log t>0$ on the whole window. $C_1>0$ is without loss of generality. $D(\mu)=0$ when $\mu^*=1$, and then both hypotheses fail. Times are natural numbers cast to reals.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 18, Theorem 8; proof §9.2, pp. 42–43

import Mathlib
import Definitions.Def_QueueBandit_EarlyLower_Model
import Definitions.Def_QueueBandit_LateLower_Dynamics

namespace QueueBandit.EarlyLower

/-- Theorem 8 (arXiv:1604.06377v4, p. 18). Fix the service probabilities `μ` (entries in `[0, 1]`,
unique optimal matching), `α ∈ (0, 1)`, an `α`-consistent policy and `γ > 1/(1 − α)`. There are
constants `τ > e` and `C₁ > 0`, the same for every arrival vector `λ`, such that for every `λ`
satisfying Assumption 2, with the initial state drawn from the stationary law of `Q*`
(Assumption 3), `T₀ = max{C₁ K^γ, τ}` and `η = (K − 1) D(μ) / (2 T₀)`:
(a) if `ε̄ = (1/U) Σ_u ε_u < η/2`, then `(1/U) Σ_u Ψ_u(t) ≥ (D(μ)/4)(K − 1) log t / log log t` for
every integer `t ∈ [T₀, (K − 1) D(μ) / (4 ε̄)]`;
(b) for every queue `u` with `ε_u < η`,
`Ψ_u(t) ≥ (D(μ)/4) max{U − 1, 2(K − U)} log t / log log t` for every integer
`t ∈ [T₀, (K − 1) D(μ) / (2 ε_u)]`.
The paper prints "τ and C₁ (independent of (λ, μ))"; its proof (p. 43) takes them from
Corollary 20, whose constants depend on the instance, so here they are chosen after `μ` and the
policy and before `λ` (the policy never observes arrivals). -/
theorem theorem_8 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (hU : 0 < U)
    (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1) (hA1 : QueueBandit.LateLower.Assumption1 mu kstar)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (π : QueueBandit.LateLower.Policy U K)
    (hπ : QueueBandit.LateLower.IsAlphaConsistent π α)
    (γ : ℝ) (hγ : 1 / (1 - α) < γ) :
    ∃ τ C₁ : ℝ, Real.exp 1 < τ ∧ 0 < C₁ ∧
      ∀ lam : Fin U → ℝ, (∀ u, 0 ≤ lam u ∧ lam u ≤ 1) → (∀ u, 0 < eps lam mu kstar u) →
        let T₀ : ℝ := max (C₁ * (K : ℝ) ^ γ) τ
        let η : ℝ := ((K : ℝ) - 1) * QueueBandit.LateLower.D mu kstar / (2 * T₀)
        let εbar : ℝ := (1 / (U : ℝ)) * ∑ u : Fin U, eps lam mu kstar u
        (εbar < η / 2 → ∀ t : ℕ, T₀ ≤ t →
          (t : ℝ) ≤ ((K : ℝ) - 1) * QueueBandit.LateLower.D mu kstar / (4 * εbar) →
          QueueBandit.LateLower.D mu kstar / 4 * ((K : ℝ) - 1) *
              (Real.log t / Real.log (Real.log t)) ≤
            (1 / (U : ℝ)) * ∑ u : Fin U,
              QueueBandit.LateLower.queueRegret lam mu kstar (initLaw lam mu kstar) π u t) ∧
        (∀ u : Fin U, eps lam mu kstar u < η → ∀ t : ℕ, T₀ ≤ t →
          (t : ℝ) ≤ ((K : ℝ) - 1) * QueueBandit.LateLower.D mu kstar / (2 * eps lam mu kstar u) →
          QueueBandit.LateLower.D mu kstar / 4 * max ((U : ℝ) - 1) (2 * ((K : ℝ) - U)) *
              (Real.log t / Real.log (Real.log t)) ≤
            QueueBandit.LateLower.queueRegret lam mu kstar (initLaw lam mu kstar) π u t) := by sorry

end QueueBandit.EarlyLower
