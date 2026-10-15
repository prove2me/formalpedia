-- Prove2me | Theorems.Thm_VehicleSharePricing_DemandFree_availability_ge_beta
-- name    : VehicleSharePricing.DemandFree.availability_ge_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:15.825836+00:00
-- url     : https://prove2.me/theorems/33bb01b9-df8d-4353-8a62-641b2274cd35
-- title:
--   Proof of Theorem 3, p. 11 — α(K) ≥ β(K) for every K ≥ 1 when the workload is at most ∆
-- statement:
--   Consider a vehicle-sharing network satisfying the standing assumptions with $N$ locations, a workload budget $\Delta>0$, and a policy $q$ feasible for Problem (2) with budget $\Delta$ (balanced flows, $\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}/\mu_{ij}\le\Delta$, $q_{ij}\in[0,1]$) that induces a strongly connected network. Let $r$ be a positive solution of (9). Then for every $K\ge1$ and every location $i$,
--
--   $$
--   \alpha_i(K)\ \ge\ \beta(K),
--   $$
--
--   where $\beta(0)=0$ and $\beta(K)=K/(N+K-1+\Delta(1-\beta(K-1)))$.
--
--   This comparison replaces the demand-dependent workload of the policy by the budget $\Delta$, which is what makes the final bound independent of demand.
--
--   **Formalization Note** The paper states the step for the optimal $q^s$ of Problem (2); its argument uses only the workload constraint (together with balance, which (5) needs), so the hypothesis is feasibility. The paper has $\Delta\ge K\ge 1$; here $\Delta>0$ suffices.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 11, proof of Theorem 3

import Mathlib
import Definitions.Def_VehicleSharePricing_DemandFree_Model
import Definitions.Def_VehicleSharePricing_DemandFree_Beta

namespace VehicleSharePricing.DemandFree
theorem availability_ge_beta {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (net : Network L) (hnet : net.Standing) (Δ : ℝ) (hΔ : 0 < Δ) (q : L → L → ℝ)
    (hfeas : net.Feasible q Δ) (hconn : net.InducesStronglyConnected q)
    (r : L → ℝ) (hr : net.IsTrafficSolution q r) (K : ℕ) (hK : 1 ≤ K) (i : L) :
    beta (Fintype.card L) Δ K ≤ net.availability q r K i := by sorry
end VehicleSharePricing.DemandFree
