-- Prove2me | Theorems.Thm_RideHailingAV_PureHV_assumption_2_positive_demand
-- name    : RideHailingAV.PureHV.assumption_2_positive_demand
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:26:30.815415+00:00
-- url     : https://prove2.me/theorems/44fde439-0c83-49e9-b4f4-09df5bf98afd
-- title:
--   Assumption 2 implies a strictly positive equilibrium demand
-- statement:
--   Consider the model with $a>0$, $0\le r<1$, $t_2>0$, $V>0$, $w_0>0$, $\alpha\ge0$, and a scenario of mass $m>0$ satisfying Assumption 2 (18). Then
--
--   1. a maximal stable equilibrium with strictly positive demand $d^*>0$ exists, and
--   2. every maximal stable equilibrium has strictly positive demand.
--
--   So HVs provide service in every scenario satisfying Assumption 2: the market does not collapse to the "thin market" equilibrium $d=0$.
--
--   Differences from the source:
--   - reading: Assumption 2: arg max_p rᵢ(dᵢ(p)) ≥ p*_HV,i → every price q ≥ 0 maximizing p ↦ rᵢ(dᵢ(p)) over p ≥ 0 is at least pᵢ(d*) for the maximal stable equilibrium d* (IsLooseMarket); reason: prices are nonnegative; the maximizer is unique (V/2), so 'the arg max is ≥ p*' means each maximizer is
--   - reading: Definition 1: there is no ε > 0 such that rᵢ(d − ε) < w(n(d − ε))n(d − ε) and rᵢ(d + ε) > w(n(d + ε))n(d + ε) → no ε > 0 with 0 ≤ d − ε and d + ε ≤ m satisfies both inequalities (IsStableHVEquilibrium); reason: keeps the arguments in the demand domain [0, mᵢ] of (3); the maximal stable equilibrium is the largest solution of (13) in [0, mᵢ] under both readings, since beyond mᵢ revenue is negative and cost positive
--   - encoding: equilibrium demand rates → IsHVEquilibrium requires 0 ≤ d ≤ m; reason: (3) defines pᵢ on [0, mᵢ] only
--   - generalization: Assumption 1 (c_v + c_f < w₀ with c_f, c_v > 0, p. 7) → 0 < w₀; reason: the pure-HV market involves no AV and uses Assumption 1 only through w₀ > 0, which Assumption 1 implies, so the statement specializes to the paper's
--   - encoding: the model constants a, t₂ (and V, mᵢ where used) of the ETA function, trip time, value support and demand mass → explicit hypotheses 0 < a, 0 < t₂ (0 < V, 0 < m where used); reason: implicit in the model: ã > 0 is stated on p. 12 and ã > 0 iff a > 0; t₂ is a trip time; V is the top of the value support [0, V]; (3) divides by mᵢ
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), §4, p. 15 (unnumbered, the paragraph after Assumption 2)

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_IsLooseMarket

namespace RideHailingAV.PureHV

/-- **Assumption 2 implies positive equilibrium demand.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), §4, p. 15 (unnumbered, after
Assumption 2): "Note Assumption 2 also implies that HVs always provide service in all scenarios
that we consider. That is, for each scenario `i`, a strictly positive equilibrium demand `d*_HV,i`
exists such that revenue `r_i(d*_HV,i)` covers the total labor cost of
`w(n(d*_HV,i))n(d*_HV,i)`."

Under the model's standing conditions, `m > 0` and Assumption 2 (in its form (18)) for the
scenario of mass `m`: a maximal stable equilibrium with strictly positive demand exists, and
every maximal stable equilibrium has strictly positive demand. -/
theorem assumption_2_positive_demand (M : Market) (ha : 0 < M.a) (hr0 : 0 ≤ M.r)
    (hr1 : M.r < 1) (ht2 : 0 < M.t2) (hV : 0 < M.V) (hw0 : 0 < M.w0) (hα : 0 ≤ M.α)
    (m : ℝ) (hm : 0 < m) (hA2 : IsLooseMarket M m) :
    (∃ d : ℝ, 0 < d ∧ IsMaxStableHVEquilibrium M m d) ∧
      ∀ d, IsMaxStableHVEquilibrium M m d → 0 < d := by sorry

end RideHailingAV.PureHV
