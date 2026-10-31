-- Prove2me | Theorems.Thm_ReservationPolicy_eq_26_27
-- name    : ReservationPolicy.eq_26_27
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:25:54.70788+00:00
-- url     : https://prove2.me/theorems/d3a09867-bf0b-4e97-97c7-418aaa9a3ebb
-- title:
--   Equations (26)–(27) — equilibrium cutoff and efforts (corrected: effort and $z$ domains)
-- statement:
--   Let the parameters satisfy the standing assumptions and suppose type-$x$ students invest. At any effort-stage outcome with seats clearing, the cutoff is $d^*$ of (26) and, writing $\Delta=(8k-\phi^2)(8k-1-\alpha)-\phi^2(1-\alpha)(8k-1)$, the efforts are
--   $$
--   e_x^*=\frac{2(1-z)(8k-\phi^2)}{\Delta},\qquad e_y^*=\frac{2(1-z)(8k-1)\phi}{\Delta}.
--   $$
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - correction: d ∈ (0,1), said to be equivalent to 4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2 (p.9) → the z-interval alone, with no bound on d (Params.Valid); reason: the two are not equivalent: k = 1, ϕ = 1/2, α = 1/2, z = 7/100 is in the interval with d* = 3427/3300 > 1; the interval is what the proof of Proposition 1 uses (p.35) and contains the region d* ∈ (0,1)
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (26)–(27), p.35

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestCandidate
import Definitions.Def_ReservationPolicy_Params_dStar

namespace ReservationPolicy

/-- **Equations (26)–(27).** At the effort stage with type `x` investing, the cutoff is `d*` and the
efforts are (27). Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eqs. (26)–(27), p.35 (PDF 35). -/
theorem eq_26_27 (P : Params) (hP : P.Valid) (b : Benchmark) (hb : IsInvestCandidate P b) :
    b.d = P.dStar ∧
    b.ex = 2 * (1 - P.z) * (8 * P.k - P.ϕ ^ 2) /
      ((8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1)) ∧
    b.ey = 2 * (1 - P.z) * (8 * P.k - 1) * P.ϕ /
      ((8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1)) := by sorry

end ReservationPolicy
