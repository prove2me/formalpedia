-- Prove2me | Theorems.Thm_ReservationPolicy_eq_47
-- name    : ReservationPolicy.eq_47
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:25.192275+00:00
-- url     : https://prove2.me/theorems/61523751-9bb8-46a1-822e-4d846a4be3ce
-- title:
--   Equation (47) — educational inequality at the benchmark (corrected: effort and $z$ domains)
-- statement:
--   Let the parameters satisfy the standing assumptions. At every effort-stage outcome with type $x$ investing, educational inequality equals
--   $$
--   EI=\frac{4k(1-z)(1-\phi^2)}{32k^2+\phi^2-4k\bigl(1+2\phi^2+\alpha(1-\phi^2)\bigr)}.
--   $$
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - correction: d ∈ (0,1), said to be equivalent to 4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2 (p.9) → the z-interval alone, with no bound on d (Params.Valid); reason: the two are not equivalent: k = 1, ϕ = 1/2, α = 1/2, z = 7/100 is in the interval with d* = 3427/3300 > 1; the interval is what the proof of Proposition 1 uses (p.35) and contains the region d* ∈ (0,1)
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (47), p.38

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestCandidate

namespace ReservationPolicy

/-- **Equation (47).** The closed form of educational inequality without the policy. Bao, Ni & Singh,
SSRN 3772113 (May 30, 2023), eq. (47), p.38 (PDF 38). -/
theorem eq_47 (P : Params) (hP : P.Valid) (b : Benchmark) (hb : IsInvestCandidate P b) :
    b.rhoX - b.rhoY P = 4 * P.k * (1 - P.z) * (1 - P.ϕ ^ 2) /
      (32 * P.k ^ 2 + P.ϕ ^ 2 - 4 * P.k * (1 + 2 * P.ϕ ^ 2 + P.α * (1 - P.ϕ ^ 2))) := by sorry

end ReservationPolicy
