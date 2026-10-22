-- Prove2me | Theorems.Thm_VehicleSharePricing_Static_eq_5
-- name    : VehicleSharePricing.Static.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:21.747637+00:00
-- url     : https://prove2.me/theorems/eaf3282a-833c-4574-8288-3d1272689f44
-- title:
--   Equation (5), p. 8 — $\alpha(K)=K/(K+N-1+(\lambda/\mu)(1-\alpha(K-1)))$
-- statement:
--   Let $q$ be a quantile policy with balanced flows that induces a strongly connected network, let $r$ be a positive solution of the traffic equations (9), and write $\alpha(K)$ for the availability at a location $i$ with $K$ vehicles. Then for every $K\ge 1$,
--   $$\alpha(K)=\frac{K}{K+N-1+\sum_{(i,j)\in\mathcal A}\dfrac{\Lambda_{ij}q_{ij}}{\mu_{ij}}\bigl(1-\alpha(K-1)\bigr)}.$$
--
--   This recursion in the number of vehicles is the engine of Theorems 1 and 2: bounding $\alpha(K-1)$ from below bounds $\alpha(K)$ from below. The paper derives it from the random observer property (arrival theorem) and Little's law.
--
--   **Formalization Note** The availability is the product-form one of the definition file, with $\alpha(0)=0$ (no vehicle can be waiting). The statement holds at every location $i$; the paper's $\alpha$ is location-free by the equal-availability milestone. It is posed for every balanced quantile policy inducing a strongly connected network, which includes $q^s$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 8, Equation (5); Appendix, pp. 23–24, "Proof for Equation (5)"

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_Model
import Definitions.Def_VehicleSharePricing_Static_Availability

namespace VehicleSharePricing.Static

/-- Equation (5), p. 8 (Appendix, pp. 23–24): under a quantile policy `q` with balanced flows
that induces a strongly connected network, for every `K ≥ 1` and every location `i`,
`α(K) = K / (K + N − 1 + (∑_{(i,j)∈𝒜} Λ_ij q_ij / μ_ij)(1 − α(K − 1)))`. -/
theorem eq_5 {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q) (hbal : Balanced P q)
    (hconn : InducesStronglyConnected P q) (r : L → ℝ) (hr : IsTrafficSolution P q r)
    (K : ℕ) (hK : 1 ≤ K) (i : L) :
    availability P q r K i =
      (K : ℝ) / ((K : ℝ) + (Fintype.card L : ℝ) - 1 +
        workload P q * (1 - availability P q r (K - 1) i)) := by sorry

end VehicleSharePricing.Static
