-- Prove2me | Theorems.Thm_VehicleSharePricing_Static_ratio_eq_availability
-- name    : VehicleSharePricing.Static.ratio_eq_availability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:07.502138+00:00
-- url     : https://prove2.me/theorems/5e9345f8-c7fe-48be-9b33-7b333e6751aa
-- title:
--   Proof of Theorem 1, pp. 7–8 — the ratio $R(q^s)/R_s(q^s)$ equals the common availability $\alpha$
-- statement:
--   Let $q$ be a quantile policy with balanced flows that induces a strongly connected network, let $r$ be a positive solution of the traffic equations (9), and assume $R_s(q)=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}I_{ij}(q_{ij})>0$. Then for every number of vehicles $K$ and every location $i$,
--   $$\frac{R(q)}{R_s(q)}=\frac{\sum_{(i,j)\in\mathcal A}\alpha_i\Lambda_{ij}q_{ij}I_{ij}(q_{ij})}{\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}I_{ij}(q_{ij})}=\alpha_i(K).$$
--
--   The static policy therefore earns exactly the fraction $\alpha$ of the fluid value, which reduces every bound of the paper to a bound on the availability.
--
--   **Formalization Note** The hypothesis $R_s(q)>0$ is added: without it the ratio is $0/0$. The paper states this for $q^s$; the statement is posed for every balanced quantile policy inducing a strongly connected network, which includes $q^s$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), pp. 7–8, proof of Theorem 1

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_Model
import Definitions.Def_VehicleSharePricing_Static_Availability

namespace VehicleSharePricing.Static

/-- Proof of Theorem 1, pp. 7–8: under a quantile policy `q` with balanced flows that induces a
strongly connected network and has `R_s(q) > 0`, the ratio `R(q)/R_s(q)` equals the common
availability `α` (the availability at any location `i`). -/
theorem ratio_eq_availability {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q) (hbal : Balanced P q)
    (hconn : InducesStronglyConnected P q) (r : L → ℝ) (hr : IsTrafficSolution P q r)
    (hRs : 0 < Rs P q) (K : ℕ) (i : L) :
    R P q r K / Rs P q = availability P q r K i := by sorry

end VehicleSharePricing.Static
