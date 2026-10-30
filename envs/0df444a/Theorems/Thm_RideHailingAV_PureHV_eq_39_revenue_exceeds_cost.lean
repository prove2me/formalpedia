-- Prove2me | Theorems.Thm_RideHailingAV_PureHV_eq_39_revenue_exceeds_cost
-- name    : RideHailingAV.PureHV.eq_39_revenue_exceeds_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:27:26.38914+00:00
-- url     : https://prove2.me/theorems/b8ee161b-1e3b-46c8-99f1-5b827f79917c
-- title:
--   Eq. (39) — a larger demand mass lifts revenue above labor cost
-- statement:
--   Let $V>0$, $t_2>0$ and potential demand masses $0<m<m'$. If $0<d\le m$ solves the equilibrium condition (13) in the scenario of mass $m$, $r_m(d)=w(\underline n(d))\underline n(d)$, then in the scenario of mass $m'$ the revenue at the same demand rate exceeds the labor cost:
--   $$r_{m'}(d)>w(\underline n(d))\,\underline n(d).\qquad(39)$$
--   The paper applies this to the equilibrium demand $d=d^*_{HV,i}$ when the mass grows from $m_i$ to $m_{i+1}$; it starts the argument that $d^*_{HV,i}$ is increasing in $m_i$ (Proposition 1, Item 2).
--
--   Differences from the source:
--   - generalization: d = d*_HV,i, the maximal stable equilibrium demand of scenario i (positive under Assumption 2) → any 0 < d ≤ m solving (13) in the scenario of mass m; reason: d*_HV,i is such a d (assumption_2_positive_demand), so the statement specializes to (39)
--   - encoding: the model constants a, t₂ (and V, mᵢ where used) of the ETA function, trip time, value support and demand mass → explicit hypotheses 0 < a, 0 < t₂ (0 < V, 0 < m where used); reason: implicit in the model: ã > 0 is stated on p. 12 and ã > 0 iff a > 0; t₂ is a trip time; V is the top of the value support [0, V]; (3) divides by mᵢ
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), Appendix B.1.3, eq. (39), p. 43

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_revenue
import Definitions.Def_RideHailingAV_PureHV_laborCost

namespace RideHailingAV.PureHV

/-- **Eq. (39) — a larger demand mass lifts revenue above cost.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), Appendix B.1.3, eq. (39),
p. 43: "Now suppose the potential demand mass increases from `m_i` to `m_{i+1}`. Then the revenue
immediately increases due to higher prices from the increased demand mass. That is,
`r_{i+1}(d*_HV,i) > w(n*_HV,i)n*_HV,i` (39)."

For `V, t₂ > 0` and masses `0 < m < m'`: if `0 < d ≤ m` solves the equilibrium condition (13)
in the scenario of mass `m`, then the revenue at `d` in the scenario of mass `m'` exceeds the
labor cost at `d`.

**Formalization Note.** The paper applies (39) to the equilibrium demand `d*_HV,i`, which is
positive under Assumption 2 (`assumption_2_positive_demand`); the statement covers every positive
solution of (13). -/
theorem eq_39_revenue_exceeds_cost (M : Market) (ht2 : 0 < M.t2) (hV : 0 < M.V)
    (m m' : ℝ) (hm : 0 < m) (hmm' : m < m') (d : ℝ) (hd : 0 < d) (hdm : d ≤ m)
    (heq : revenue M m d = laborCost M d) :
    laborCost M d < revenue M m' d := by sorry

end RideHailingAV.PureHV
