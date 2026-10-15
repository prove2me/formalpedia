-- Prove2me | Theorems.Thm_VehicleSharePricing_Static_B_K_K_eq_availability
-- name    : VehicleSharePricing.Static.B_K_K_eq_availability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:24.982286+00:00
-- url     : https://prove2.me/theorems/13ef4373-3bb4-4329-afd1-22f6427f2229
-- title:
--   Proof of Theorem 2, p. 10 — $B^K_K(q^s)=\alpha(K)$
-- statement:
--   Let $q$ be a quantile policy with balanced flows that induces a strongly connected network, with workload $\lambda/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}/\mu_{ij}$, and let $r$ be a positive solution of the traffic equations (9). Then for every number of vehicles $K\ge 0$ and every location $l$, the last term of the bound sequence equals the availability:
--   $$B^K_K(q)=\alpha_l(K),$$
--   where $B^K_i(q)$ is the bound sequence of Theorem 2 with $\rho=\lambda/\mu$.
--
--   So the bounds $B^K_i(q^s)$ end at the exact value of the ratio $R(q^s)/R_s(q^s)$.
--
--   **Formalization Note** $B^0_0=0=\alpha(0)$ is included ($K=0$). Posed for every balanced quantile policy inducing a strongly connected network, which includes $q^s$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 10, proof of Theorem 2

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_Model
import Definitions.Def_VehicleSharePricing_Static_Availability
import Definitions.Def_VehicleSharePricing_Static_BoundSeq

namespace VehicleSharePricing.Static

/-- Proof of Theorem 2, p. 10: `B^K_K(q^s) = α(K)`. For a quantile policy `q` with balanced
flows that induces a strongly connected network, with `λ/μ` its workload, the last term
`B^K_K(q)` of the bound sequence with `ρ = λ/μ` equals the availability `α(K)` at every
location, for every number of vehicles `K`. -/
theorem B_K_K_eq_availability {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q) (hbal : Balanced P q)
    (hconn : InducesStronglyConnected P q) (r : L → ℝ) (hr : IsTrafficSolution P q r)
    (K : ℕ) (l : L) :
    Bseq (Fintype.card L) (workload P q) K K = availability P q r K l := by sorry

end VehicleSharePricing.Static
