-- Prove2me | Theorems.Thm_VehicleSharePricing_DemandFree_ratio_eq_availability
-- name    : VehicleSharePricing.DemandFree.ratio_eq_availability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:13.603984+00:00
-- url     : https://prove2.me/theorems/4aa07f76-f03e-4e13-832a-686d7240c5a9
-- title:
--   Proof of Theorem 1, pp. 7–8 — the ratio R(q^s)/R_s(q^s) equals the common availability α
-- statement:
--   Under the hypotheses of the equal-availability statement (standing assumptions, $q_{ij}\in[0,1]$ on $\mathcal A$, balanced flows, a strongly connected induced network, a positive solution $r$ of (9)), suppose moreover that the fluid reward is positive, $R_s(q)>0$. Then for every location $i$ and every number of vehicles $K$,
--
--   $$
--   \frac{R(q)}{R_s(q)}=\frac{\sum_{(i,j)\in\mathcal A}\alpha_i\Lambda_{ij}q_{ij}I_{ij}(q_{ij})}{\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}I_{ij}(q_{ij})}=\alpha_i(K).
--   $$
--
--   It turns the performance ratio of the static policy into a single availability, the quantity that the recursion (5) and all bounds of the paper control.
--
--   **Formalization Note** The hypothesis $R_s(q)>0$ is added: with $R_s(q)=0$ the paper's ratio is $0/0$, which Lean evaluates to $0$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), pp. 7–8, proof of Theorem 1

import Mathlib
import Definitions.Def_VehicleSharePricing_DemandFree_Model

namespace VehicleSharePricing.DemandFree
theorem ratio_eq_availability {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (net : Network L) (hnet : net.Standing) (q : L → L → ℝ)
    (hq : ∀ i j, 0 < net.Λ i j → q i j ∈ Set.Icc (0 : ℝ) 1) (hbal : net.Balanced q)
    (hconn : net.InducesStronglyConnected q) (r : L → ℝ) (hr : net.IsTrafficSolution q r)
    (hRs : 0 < net.Rs q) (K : ℕ) (i : L) :
    net.R q r K / net.Rs q = net.availability q r K i := by sorry
end VehicleSharePricing.DemandFree
