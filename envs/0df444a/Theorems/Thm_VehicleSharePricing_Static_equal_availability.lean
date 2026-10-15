-- Prove2me | Theorems.Thm_VehicleSharePricing_Static_equal_availability
-- name    : VehicleSharePricing.Static.equal_availability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:14.540598+00:00
-- url     : https://prove2.me/theorems/37bd8038-3287-490f-aab7-ef168a51d274
-- title:
--   Proof of Theorem 1, p. 7 (Appendix, p. 23) — balanced flows give equal availability at every location
-- statement:
--   Let $q$ be a quantile policy ($q_{ij}\in[0,1]$ on $\mathcal A$) with **balanced flows**, $\sum_j\Lambda_{ij}q_{ij}=\sum_j\Lambda_{ji}q_{ji}$ for every location $i$, which induces a strongly connected network, and let $r$ be a positive solution of the traffic equations (9). Then for every number of vehicles $K$ the product-form availability is the same at all locations:
--   $$\alpha_i(K)=\alpha_j(K)\qquad\text{for all locations } i,j.$$
--
--   The common value is the paper's $\alpha$ (or $\alpha(K)$). It is what lets the reward rate $R(q)$ of (3) factor as $\alpha R_s(q)$.
--
--   **Formalization Note** The paper asserts this for the optimal static policy $q^s$, and its Appendix proves it "when the network is balanced"; the statement is posed for every balanced quantile policy inducing a strongly connected network, which includes $q^s$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 7, proof of Theorem 1; p. 23, Appendix, "Proof for α_i = α_j = α when the network is balanced"

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_Model
import Definitions.Def_VehicleSharePricing_Static_Availability

namespace VehicleSharePricing.Static

/-- Proof of Theorem 1, p. 7, proved in the Appendix, p. 23: under a quantile policy `q` with
balanced flows that induces a strongly connected network, the availability `α_i` with `K`
vehicles is the same at every location. -/
theorem equal_availability {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q) (hbal : Balanced P q)
    (hconn : InducesStronglyConnected P q) (r : L → ℝ) (hr : IsTrafficSolution P q r)
    (K : ℕ) (i j : L) :
    availability P q r K i = availability P q r K j := by sorry

end VehicleSharePricing.Static
