-- Prove2me | Theorems.Thm_VehicleSharePricing_DemandFree_theorem_3
-- name    : VehicleSharePricing.DemandFree.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:22.928746+00:00
-- url     : https://prove2.me/theorems/b1526225-7415-4d1e-8a2e-c38f31f8155f
-- title:
--   Theorem 3, p. 10 (static half) — with ∆ = K, R(q^s)/R_s(q^s) ≥ 1 − (√((c+1)²−1) − c), c = (N−1)/(2K) + 1/(2(N+K))
-- statement:
--   Consider a vehicle-sharing network with $N$ locations satisfying the standing assumptions, and $K\ge1$ vehicles. Let $q^s$ be an optimal solution of Problem (2) with workload budget $\Delta=K$, inducing a strongly connected network, with positive fluid reward $R_s(q^s)>0$, and let $r$ be any positive solution of the traffic equations (9). Then the expected reward rate $R(q^s)$ of Equation (3) satisfies
--
--   $$
--   \frac{R(q^s)}{R_s(q^s)}\ \ge\ 1-\left(\sqrt{\Bigl(\frac{N-1}{2K}+\frac{1}{2(N+K)}+1\Bigr)^2-1}\;-\;\Bigl(\frac{N-1}{2K}+\frac{1}{2(N+K)}\Bigr)\right).
--   $$
--
--   The bound depends only on $N$ and $K$, not on demand rates or travel times, and it tends to $1$ at rate $1-O(1/\sqrt K)$.
--
--   **Scope: this is the static half of Theorem 3.** The paper states the bound for $R(q^s)/R(q^*)$, where $q^*$ is an optimal state-dependent (dynamic) policy, and obtains it from the present inequality together with $R(q^*)\le R_s(q^s)$ (Proposition 1, p. 6). Proposition 1 needs the stationary analysis of arbitrary dynamic policies and is not part of this mission; the present inequality implies the paper's statement once it is available.
--
--   **Formalization Note** The paper's sentence does not say which $\Delta$ is used; its proof takes "the pricing policy $q^s$ corresponding to $\Delta=K$" (p. 10), so $\Delta=K$ is a hypothesis. $R_s(q^s)>0$ is added because the ratio is otherwise $0/0$. The commentary "$=1-O(1/\sqrt K)$" is not formalized. The paper's argument uses only feasibility of $q^s$ and strong connectivity, not optimality.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 10, Theorem 3 (proof pp. 10–11)

import Mathlib
import Definitions.Def_VehicleSharePricing_DemandFree_Model

namespace VehicleSharePricing.DemandFree
theorem theorem_3 {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (net : Network L) (hnet : net.Standing) (K : ℕ) (hK : 1 ≤ K) (qs : L → L → ℝ)
    (hopt : net.IsOptimal qs (K : ℝ)) (hconn : net.InducesStronglyConnected qs)
    (hRs : 0 < net.Rs qs) (r : L → ℝ) (hr : net.IsTrafficSolution qs r) :
    1 - (Real.sqrt ((((Fintype.card L : ℝ) - 1) / (2 * K) +
            1 / (2 * ((Fintype.card L : ℝ) + K)) + 1) ^ 2 - 1) -
          (((Fintype.card L : ℝ) - 1) / (2 * K) + 1 / (2 * ((Fintype.card L : ℝ) + K))))
      ≤ net.R qs r K / net.Rs qs := by sorry
end VehicleSharePricing.DemandFree
