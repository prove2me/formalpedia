-- Prove2me | Theorems.Thm_SmartExpedite_PolicyM_theorem_1
-- name    : SmartExpedite.PolicyM.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:42.114692+00:00
-- url     : https://prove2.me/theorems/e3f977cd-2c98-475c-9441-a0e24a296859
-- title:
--   Theorem 1, p. 18 — Policy-M state space and product-form stationary distribution
-- statement:
--   Consider $K\ge1$ service nodes with positive Poisson demand rate $\lambda$ and positive exponential service rates $\mu_1,\ldots,\mu_K$. Let $u$ be Policy-M parameters satisfying Assumption A. Using exactly the sourcing and expediting rules of (7) and §4, the states reachable from the empty system are
--
--   $$S_M(u)=\{n\in\mathbb N^K:n[k+1,l]\le u_{kl}\text{ whenever }0\le k<l\le K\}.$$
--
--   If $\lambda<\mu_K$ and $u_{0i}<\infty$ for $1\le i<K$, the weights in (12) are summable, their normalizer $G(u)$ is positive, and
--
--   $$\pi_M(n)=\frac{\mathbf1_{S_M(u)}(n)}{G(u)}\prod_{k=1}^{K}\left(\frac{\lambda}{\mu_k}\right)^{n_k}$$
--
--   is a probability distribution satisfying the global balance equations for the explicit Policy-M transition rates. The result identifies the feasible occupancy states and supplies the product-form equilibrium weights used to evaluate the inventory policy.
--
--   **Formalization Note** The source defines its stationary distribution by a continuous-time Markov-chain limit in (8). Here stationarity is encoded by normalization and global balance. Identification with that limit and uniqueness are not included. Thresholds are extended natural numbers to represent the paper's infinite terminal entries; the condition $K\ge1$ is implicit in its numbered-node model.
-- source:
--   Song, Xiao, Zhang & Zipkin, Smart policies for multi-source inventory systems and general tandem queues with order tracking and expediting, SSRN 3702068 (version of September 28, 2020), p. 18, Theorem 1, (11)–(12)

import Mathlib
import Definitions.Def_SmartExpedite_PolicyM_Model

namespace SmartExpedite.PolicyM

/-- Theorem 1, p. 18. The state space is the set reachable from the empty
system through positive-rate Policy-M transitions. The product form is
expressed as a normalized probability vector satisfying global balance for
the explicit Policy-M rates; the paper's CTMC limiting interpretation of (8)
is not encoded. -/
theorem theorem_1 (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (hK : 1 ≤ K) (hlam : 0 < lam)
    (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hu : IsPolicyParam K u) (hA : AssumptionA K u) :
    {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u ∧
    (lam < mu K →
      (∀ i, 1 ≤ i → i ≤ K - 1 → u 0 i ≠ ⊤) →
      Summable ((SM K u).indicator (weight K lam mu)) ∧
      0 < normG K u lam mu ∧
      HasSum (piM K u lam mu) 1 ∧
      ∀ n, piM K u lam mu n * outRate K lam mu n =
        ∑' m, piM K u lam mu m * rate K u lam mu m n) := by sorry

end SmartExpedite.PolicyM
