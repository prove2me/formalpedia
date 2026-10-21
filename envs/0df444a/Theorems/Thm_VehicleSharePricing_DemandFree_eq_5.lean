-- Prove2me | Theorems.Thm_VehicleSharePricing_DemandFree_eq_5
-- name    : VehicleSharePricing.DemandFree.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:19.669642+00:00
-- url     : https://prove2.me/theorems/c06560f5-691a-4039-b183-b86d08717eb0
-- title:
--   Equation (5), p. 8 — α(K) = K/(K+N−1+(λ/μ)(1−α(K−1)))
-- statement:
--   Under the hypotheses of the equal-availability statement (standing assumptions, $q_{ij}\in[0,1]$ on $\mathcal A$, balanced flows, a strongly connected induced network, a positive solution $r$ of (9)), let $\alpha(K)$ denote the availability at any location with $K$ vehicles and $N=|\mathcal N|$. Then for every $K\ge 1$,
--
--   $$
--   \alpha(K)=\frac{K}{K+N-1+\sum_{(i,j)\in\mathcal A}\frac{\Lambda_{ij}q_{ij}}{\mu_{ij}}\,\bigl(1-\alpha(K-1)\bigr)}. \tag{5}
--   $$
--
--   The recursion relates the system with $K$ vehicles to the system with $K-1$ vehicles; every bound of the paper is obtained by bounding $\alpha(K-1)$ in it.
--
--   **Formalization Note** The statement is made at every location $i$, with $\alpha_i$ on both sides. $\alpha(0)=0$ follows from the definition (with no vehicles no location is occupied). $K-1$ is natural-number subtraction under $K\ge 1$; $K+N-1$ is computed in $\mathbb R$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 8, Equation (5); Appendix, pp. 23–24, 'Proof for Equation (5)'

import Mathlib
import Definitions.Def_VehicleSharePricing_DemandFree_Model

namespace VehicleSharePricing.DemandFree
theorem eq_5 {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (net : Network L) (hnet : net.Standing) (q : L → L → ℝ)
    (hq : ∀ i j, 0 < net.Λ i j → q i j ∈ Set.Icc (0 : ℝ) 1) (hbal : net.Balanced q)
    (hconn : net.InducesStronglyConnected q) (r : L → ℝ) (hr : net.IsTrafficSolution q r)
    (K : ℕ) (hK : 1 ≤ K) (i : L) :
    net.availability q r K i =
      (K : ℝ) / ((K : ℝ) + (Fintype.card L : ℝ) - 1 +
        net.workload q * (1 - net.availability q r (K - 1) i)) := by sorry
end VehicleSharePricing.DemandFree
