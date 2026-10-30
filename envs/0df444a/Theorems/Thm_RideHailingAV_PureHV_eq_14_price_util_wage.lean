-- Prove2me | Theorems.Thm_RideHailingAV_PureHV_eq_14_price_util_wage
-- name    : RideHailingAV.PureHV.eq_14_price_util_wage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:28:57.408772+00:00
-- url     : https://prove2.me/theorems/404a80b9-c2a4-48bd-875c-f94aa30876c0
-- title:
--   Eq. (14) — equilibrium condition in price–utilization form
-- statement:
--   Let $t_1(s)=as^{-r}$ with $a>0$, $0\le r<1$, trip time $t_2>0$, and a scenario of mass $m>0$. For every demand rate $0<d\le m$, the equilibrium condition (13) holds if and only if
--   $$p_i(d)\,\bar u(d)=w(\underline n(d)).\qquad(14)$$
--   Read at an equilibrium with positive demand, (14) gives the price formula (17), $p^*=w(n^*)/u^*$.
--
--   Differences from the source:
--   - reading: divide both sides of (13) by n(d_HV) to obtain (14); use both conditions interchangeably when d_HV > 0 → (13) ↔ (14) for 0 < d ≤ m; reason: 'interchangeably' is an equivalence; n(d) > 0 for d > 0
--   - encoding: the model constants a, t₂ (and V, mᵢ where used) of the ETA function, trip time, value support and demand mass → explicit hypotheses 0 < a, 0 < t₂ (0 < V, 0 < m where used); reason: implicit in the model: ã > 0 is stated on p. 12 and ã > 0 iff a > 0; t₂ is a trip time; V is the top of the value support [0, V]; (3) divides by mᵢ
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), §4, eq. (14), p. 13

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_revenue
import Definitions.Def_RideHailingAV_PureHV_laborCost
import Definitions.Def_RideHailingAV_PureHV_util

namespace RideHailingAV.PureHV

/-- **Eq. (14) — the equilibrium condition in price–utilization form.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), §4, eq. (14),
p. 13: "When the demand rate `d_HV > 0`, we can divide both sides of Eq. (13) by `n(d_HV)` and
obtain the following equation: `p_i(d_HV)ū(d_HV) = w(n(d_HV))` (14) … We use both equilibrium
conditions interchangeably when the demand rate `d_HV > 0`."

For `a > 0`, `0 ≤ r < 1`, `t₂ > 0`, `m > 0` and `0 < d ≤ m`: (13) `r_i(d) = w(n(d))n(d)` holds
if and only if (14) `p_i(d)ū(d) = w(n(d))` holds. -/
theorem eq_14_price_util_wage (M : Market) (ha : 0 < M.a) (hr0 : 0 ≤ M.r) (hr1 : M.r < 1)
    (ht2 : 0 < M.t2) (m : ℝ) (hm : 0 < m) (d : ℝ) (hd : 0 < d) (hdm : d ≤ m) :
    revenue M m d = laborCost M d ↔ invDemand M m d * util M d = wage M (minSupply M d) := by sorry

end RideHailingAV.PureHV
