-- Prove2me | Theorems.Thm_VehicleSharePricing_DemandFree_equal_availability
-- name    : VehicleSharePricing.DemandFree.equal_availability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:11.952021+00:00
-- url     : https://prove2.me/theorems/c87cd037-df28-4c61-a5e5-32ec8f983bcb
-- title:
--   Proof of Theorem 1, p. 7 (Appendix, p. 23) — balanced static prices give the same availability at every location
-- statement:
--   Consider a vehicle-sharing network satisfying the standing assumptions, with $K$ vehicles, and a static policy $q$ with $q_{ij}\in[0,1]$ on $\mathcal A$ whose flows are balanced,
--
--   $$
--   \sum_{j\in\mathcal N}\Lambda_{ij}q_{ij}=\sum_{j\in\mathcal N}\Lambda_{ji}q_{ji}\quad\text{for all } i\in\mathcal N,
--   $$
--
--   and which induces a strongly connected network. Let $r$ be any positive solution of the traffic equations (9). Then the availabilities of the induced BCMP network are equal at all locations:
--
--   $$
--   \alpha_i(K)=\alpha_j(K)\qquad\text{for all } i,j\in\mathcal N.
--   $$
--
--   This is what allows the paper to speak of *the* availability $\alpha$ of the static policy and to reduce the performance ratio to a single number.
--
--   **Formalization Note** The statement holds for every $K\in\mathbb N$ (at $K=0$ both sides are $0$). Optimality of $q$ is not assumed: the paper's argument uses only balance and strong connectivity.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 7, proof of Theorem 1; Appendix, p. 23, 'Proof for α_i = α_j = α when the network is balanced'

import Mathlib
import Definitions.Def_VehicleSharePricing_DemandFree_Model

namespace VehicleSharePricing.DemandFree
theorem equal_availability {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (net : Network L) (hnet : net.Standing) (q : L → L → ℝ)
    (hq : ∀ i j, 0 < net.Λ i j → q i j ∈ Set.Icc (0 : ℝ) 1) (hbal : net.Balanced q)
    (hconn : net.InducesStronglyConnected q) (r : L → ℝ) (hr : net.IsTrafficSolution q r)
    (K : ℕ) (i j : L) :
    net.availability q r K i = net.availability q r K j := by sorry
end VehicleSharePricing.DemandFree
