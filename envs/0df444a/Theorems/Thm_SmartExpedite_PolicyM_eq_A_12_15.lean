-- Prove2me | Theorems.Thm_SmartExpedite_PolicyM_eq_A_12_15
-- name    : SmartExpedite.PolicyM.eq_A_12_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:29.9334+00:00
-- url     : https://prove2.me/theorems/261daf14-90e0-408f-91d0-2440678b62a0
-- title:
--   (A-12)–(A-15), p. 35 — Policy-M product weights satisfy local balance
-- statement:
--   Let $K\ge2$. Take positive arrival and service rates $\lambda,\mu_1,\ldots,\mu_K$ and Policy-M thresholds $u$ satisfying Assumption A. Suppose $\lambda<\mu_K$ and $u_{0i}<\infty$ for $1\le i<K$. Let $\pi_M$ be the normalized product form (12). For each $n\in S_M(u)$, the flow through node $K$ obeys
--
--   $$\lambda\pi_M(n)=\mu_K\pi_M(n+e_K).$$
--
--   For every occupied receiving node, the corresponding input from routed arrivals and upstream service completions equals its service output, with the predecessor terms and routing indicators displayed in (A-13), (A-14), and (A-15). Together these are the four local balance relations used for Theorem 1.
--
--   **Formalization Note** The separate node-1 and node-$K$ formulas require $K\ge2$. The occupancy guard on the receiving-node formulas gives the printed service indicator its intended meaning with natural-number state vectors. The convergence assumptions ensure that the normalizer represents a genuine probability law.
-- source:
--   Song, Xiao, Zhang & Zipkin, Smart policies for multi-source inventory systems and general tandem queues with order tracking and expediting, SSRN 3702068 (version of September 28, 2020), p. 35, (A-12)–(A-15)

import Mathlib
import Definitions.Def_SmartExpedite_PolicyM_Model

namespace SmartExpedite.PolicyM

attribute [local instance] Classical.propDecidable

/-- Equations (A-12)–(A-15), p. 35. The equations for receiving node `i`
are stated when that node is occupied, as the printed service indicator
requires. `2 ≤ K` keeps nodes 1 and K distinct. -/
theorem eq_A_12_15 (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (hK : 2 ≤ K) (hlam : 0 < lam)
    (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hu : IsPolicyParam K u) (hA : AssumptionA K u)
    (hstable : lam < mu K)
    (hfinite : ∀ i, 1 ≤ i → i ≤ K - 1 → u 0 i ≠ ⊤) :
    (∀ n ∈ SM K u,
      lam * piM K u lam mu n = mu K * piM K u lam mu (n + ev K K)) ∧
    (∀ n ∈ SM K u, 0 < occ n 1 →
      mu 1 * piM K u lam mu n =
        (if n - ev K 1 ∈ Rset K u 1
         then lam * piM K u lam mu (n - ev K 1) else 0)) ∧
    (∀ i, 2 ≤ i → i ≤ K - 1 → ∀ n ∈ SM K u, 0 < occ n i →
      mu i * piM K u lam mu n =
        (if n - ev K i ∈ Rset K u i
         then lam * piM K u lam mu (n - ev K i) else 0) +
        ∑ m ∈ Finset.Icc 1 (i - 1),
          (if n + ev K m - ev K i ∈ Eset K u m i
           then mu m * piM K u lam mu (n + ev K m - ev K i) else 0)) ∧
    (∀ n ∈ SM K u, 0 < occ n K →
      mu K * piM K u lam mu n =
        (if n - ev K K ∈ Rset K u K
         then lam * piM K u lam mu (n - ev K K) else 0) +
        (∑ m ∈ Finset.Icc 1 (K - 2),
          (if n + ev K m - ev K K ∈ Eset K u m K
           then mu m * piM K u lam mu (n + ev K m - ev K K) else 0)) +
        (if n + ev K (K - 1) - ev K K ∈ SM K u
         then mu (K - 1) * piM K u lam mu (n + ev K (K - 1) - ev K K)
         else 0)) := by sorry

end SmartExpedite.PolicyM
