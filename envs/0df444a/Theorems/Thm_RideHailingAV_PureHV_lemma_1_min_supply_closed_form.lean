-- Prove2me | Theorems.Thm_RideHailingAV_PureHV_lemma_1_min_supply_closed_form
-- name    : RideHailingAV.PureHV.lemma_1_min_supply_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:23:41.020456+00:00
-- url     : https://prove2.me/theorems/1a515b85-ba5b-4413-9ad3-2a28953b73ea
-- title:
--   Lemma 1, Item 1 — closed form of the minimal supply $\underline n(d)$
-- statement:
--   Let $t_1(s)=as^{-r}$ with $a>0$ and $0\le r<1$, and let the trip time be $t_2>0$. For every demand level $d\ge0$, the minimal supply level $\underline n(d)=\min_s\{s+d(t_1(s)+t_2)\}$ is
--   $$\underline n(d)=\tilde a\,d^{\frac1{r+1}}+t_2d,\qquad \tilde a=r^{\frac1{r+1}}a^{\frac1{r+1}}+r^{-\frac r{r+1}}a^{\frac1{r+1}}.$$
--   Moreover, when $r>0$ and $d>0$ the minimum is attained at some number of open cars $s>0$.
--
--   This closed form turns the equilibrium condition (13) into an explicit one-variable equation and gives the fleet-size formula of Proposition 1, Item 1.
--
--   Differences from the source:
--   - encoding: for any demand level d → for every d ≥ 0; reason: demand levels are nonnegative rates
--   - encoding: there exists a unique minimal supply level n(d) = min_s {s + d(t₁(s) + t₂)} → the infimum over s > 0 equals the closed form, and is attained at some s > 0 when r > 0 and d > 0; reason: minSupply is the infimum over s > 0; the attainment clause states that it is a minimum where the paper's minimizer (26) is positive; at r = 0 or d = 0 the paper's minimizer is s = 0, where the infimum has the same value
--   - encoding: the model constants a, t₂ (and V, mᵢ where used) of the ETA function, trip time, value support and demand mass → explicit hypotheses 0 < a, 0 < t₂ (0 < V, 0 < m where used); reason: implicit in the model: ã > 0 is stated on p. 12 and ã > 0 iff a > 0; t₂ is a trip time; V is the top of the value support [0, V]; (3) divides by mᵢ
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), Lemma 1, Item 1, p. 38 (proof eqs. (23)–(29), pp. 38–39)

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_minSupply
import Definitions.Def_RideHailingAV_PureHV_aTilde

namespace RideHailingAV.PureHV

/-- **Lemma 1, Item 1 — closed form of the minimal supply `n(d)`.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), Lemma 1, Item 1,
p. 38 (also eq. (12), p. 12; proof eqs. (23)–(29), pp. 38–39).

For `t₁(s) = a s^(−r)` with `a > 0`, `0 ≤ r < 1`, and trip time `t₂ > 0`, for every demand level
`d ≥ 0`:
1. the minimal supply level `n(d) = min_s {s + d(t₁(s) + t₂)}` equals `ã d^(1/(r+1)) + t₂ d`;
2. when `r > 0` and `d > 0` the minimum over open cars `s > 0` is attained (at
   `s = (ra)^(1/(r+1)) d^(1/(r+1))`, eq. (26)).

**Formalization Note.** `minSupply` is the infimum over `s > 0` (see its docstring); clause 2
records that it is a minimum where the paper's minimizer lies in `s > 0`. At `r = 0` or `d = 0`
the paper's minimizer is `s = 0`. `a > 0` is the paper's `ã > 0` (p. 12); `t₂ > 0` is a trip
time. -/
theorem lemma_1_min_supply_closed_form (M : Market) (ha : 0 < M.a) (hr0 : 0 ≤ M.r)
    (hr1 : M.r < 1) (ht2 : 0 < M.t2) (d : ℝ) (hd : 0 ≤ d) :
    minSupply M d = aTilde M * d ^ (1 / (M.r + 1)) + M.t2 * d ∧
      (0 < M.r → 0 < d →
        ∃ s : ℝ, 0 < s ∧ s + d * (M.a * s ^ (-M.r) + M.t2) = minSupply M d) := by sorry

end RideHailingAV.PureHV
