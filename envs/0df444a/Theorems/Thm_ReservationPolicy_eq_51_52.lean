-- Prove2me | Theorems.Thm_ReservationPolicy_eq_51_52
-- name    : ReservationPolicy.eq_51_52
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:23.133234+00:00
-- url     : https://prove2.me/theorems/f9a698af-5032-486b-9433-ec9e263d9cf6
-- title:
--   Equations (51)–(52) — cutoffs under a transfer (corrected: effort and $z$ domains)
-- statement:
--   Let the parameters satisfy the standing assumptions, let $b$ be the outcome without the policy, and let $o$ be an equilibrium under a transfer of $s$ seats. Then
--   $$
--   d_x=d^*+\frac{s(8k-1)}{\alpha(4k-1)},\qquad d_y=d^*-\frac{s(8k-\phi^2)}{(1-\alpha)(4k-\phi^2)}.
--   $$
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - correction: d ∈ (0,1), said to be equivalent to 4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2 (p.9) → the z-interval alone, with no bound on d (Params.Valid); reason: the two are not equivalent: k = 1, ϕ = 1/2, α = 1/2, z = 7/100 is in the interval with d* = 3427/3300 > 1; the interval is what the proof of Proposition 1 uses (p.35) and contains the region d* ∈ (0,1)
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (51)–(52), p.39

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestCandidate
import Definitions.Def_ReservationPolicy_IsPolicyEq
import Definitions.Def_ReservationPolicy_Params_dX
import Definitions.Def_ReservationPolicy_Params_dY

namespace ReservationPolicy

/-- **Equations (51)–(52).** The equilibrium cutoffs under a transfer of `s` seats. Bao, Ni & Singh,
SSRN 3772113 (May 30, 2023), eqs. (51)–(52), p.39 (PDF 39). -/
theorem eq_51_52 (P : Params) (hP : P.Valid) (b : Benchmark) (hb : IsInvestCandidate P b)
    (s : ℝ) (o : PolicyOutcome) (ho : IsPolicyEq P b s o) :
    o.dx = P.dX s ∧ o.dy = P.dY s := by sorry

end ReservationPolicy
