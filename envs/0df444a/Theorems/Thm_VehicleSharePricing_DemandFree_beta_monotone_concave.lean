-- Prove2me | Theorems.Thm_VehicleSharePricing_DemandFree_beta_monotone_concave
-- name    : VehicleSharePricing.DemandFree.beta_monotone_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:27.637973+00:00
-- url     : https://prove2.me/theorems/446553a1-a943-4766-b169-e37054a4948f
-- title:
--   Proof of Theorem 3, p. 10 — β(K) is non-decreasing and concave in K
-- statement:
--   Let $N\ge 1$ be an integer and $\Delta>0$, and let $\beta(0)=0$, $\beta(K)=K/(N+K-1+\Delta(1-\beta(K-1)))$ for $K\ge1$. Then $\beta$ is non-decreasing and concave on $\mathbb N$:
--
--   $$
--   \beta(K)\le\beta(K+1)\quad(K\ge 0),\qquad \beta(K+1)-\beta(K)\le\beta(K)-\beta(K-1)\quad(K\ge 1).
--   $$
--
--   The paper does not prove this; it refers to George and Xia (2011) and Shanthikumar and Yao (1988), who show that the throughput of a closed queueing network is non-decreasing and concave in the population. At $N=1$, $\beta$ is one minus the Erlang loss probability with offered load $\Delta$, so the statement includes the concavity of the Erlang-B carried load in the number of servers.
--
--   **Formalization Note** Concavity of a sequence is stated through its increments; $K-1$ appears only under $K\ge 1$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 10, proof of Theorem 3

import Mathlib
import Definitions.Def_VehicleSharePricing_DemandFree_Beta

namespace VehicleSharePricing.DemandFree
theorem beta_monotone_concave (N : ℕ) (hN : 1 ≤ N) (Δ : ℝ) (hΔ : 0 < Δ) :
    Monotone (beta N Δ) ∧
      ∀ K : ℕ, 1 ≤ K → beta N Δ (K + 1) - beta N Δ K ≤ beta N Δ K - beta N Δ (K - 1) := by sorry
end VehicleSharePricing.DemandFree
