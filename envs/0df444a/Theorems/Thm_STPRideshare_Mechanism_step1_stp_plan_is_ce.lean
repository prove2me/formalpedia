-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_step1_stp_plan_is_ce
-- name    : STPRideshare.Mechanism.step1_stp_plan_is_ce
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:01.496222+00:00
-- url     : https://prove2.me/theorems/7a45082d-709b-4062-851f-3d314118ebcc
-- title:
--   Proof of Theorem 2, Step 1, p. 53 — the STP prices (28) make every welfare-optimal plan a CE, with driver utilities Φ_{D_i}
-- statement:
--   Let $E$ be a valid economy, $(x,\tilde z)$ a welfare-optimal dispatching, and $p$ the STP prices of $E$:
--   $$p_{a,b,t}=\Phi_{a,t}-\Phi_{b,t+\delta(a,b)}+c_{a,b,t},\qquad \Phi_{a,t}=W(\mathcal D\cup\{(1,a,t)\})-W(\mathcal D).$$
--   Then the plan $(x,\tilde z,p)$ forms a competitive equilibrium, and the utility of every driver $i$ in it equals $\Phi_{D_i}$, the welfare gain from a replica of $i$.
--
--   This is the static core of Theorem 2: the plan the STP mechanism computes at any planning step is a driver-pessimal CE.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 53, proof of Theorem 2, Step 1

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Model

namespace STPRideshare.Mechanism

/-- Proof of Theorem 2, Step 1, p. 53: for every welfare-optimal dispatching `(x, z̃)`, the plan
with the STP prices (28), `p_{a,b,t} = Φ_{a,t} − Φ_{b,t+δ(a,b)} + c_{a,b,t}`, is a CE, and every
driver's utility in it is `Φ_{D_i}`. -/
theorem step1_stp_plan_is_ce {L ι κ : Type} [Fintype L] [Fintype ι] [Fintype κ]
    (e : Econ L ι κ) (he : e.Valid) (d : Dispatch e) (hd : d.IsWelfareOptimal) :
    d.IsCE e.stpPrice ∧ ∀ i, (d.withPrices e.stpPrice).driverUtil i = PhiD e i := by sorry

end STPRideshare.Mechanism
