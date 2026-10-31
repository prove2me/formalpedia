-- Prove2me | Theorems.Thm_ReservationPolicy_eq_55
-- name    : ReservationPolicy.eq_55
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:20.23717+00:00
-- url     : https://prove2.me/theorems/d0abe35d-bd60-45d9-88f0-ad8033f8732d
-- title:
--   Equation (55) — overall welfare as a concave quadratic in $s$ (corrected: effort and $z$ domains)
-- statement:
--   Let the parameters satisfy the standing assumptions. At every equilibrium under a transfer of $s$ seats, with $d_x^*,d_y^*$ the cutoffs (51)–(52), overall welfare is
--   $$
--   U=\alpha\Bigl[\tfrac14\Bigl(1-d_x^*+\tfrac{1+d_x^*}{8k-1}\Bigr)\Bigl(1+d_x^*+\tfrac{1+d_x^*}{8k-1}\Bigr)-k\Bigl(\tfrac{1+d_x^*}{8k-1}\Bigr)^2-\kappa\Bigr]
--   +(1-\alpha)\Bigl[\tfrac14\Bigl(1-d_y^*+\tfrac{\phi^2(1+d_y^*)}{8k-\phi^2}\Bigr)\Bigl(1+d_y^*+\tfrac{\phi^2(1+d_y^*)}{8k-\phi^2}\Bigr)-k\Bigl(\tfrac{\phi(1+d_y^*)}{8k-\phi^2}\Bigr)^2\Bigr],
--   $$
--   and $U=as^2+c_1s+c_0$ with $a<0$ independent of $s$.
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - correction: d ∈ (0,1), said to be equivalent to 4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2 (p.9) → the z-interval alone, with no bound on d (Params.Valid); reason: the two are not equivalent: k = 1, ϕ = 1/2, α = 1/2, z = 7/100 is in the interval with d* = 3427/3300 > 1; the interval is what the proof of Proposition 1 uses (p.35) and contains the region d* ∈ (0,1)
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
--   - generalization: the expression (55), and the remark that the second-order condition is satisfied (p.41) → the expression, plus a strictly negative leading coefficient in s; reason: this is what the page's second-order condition says
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (55), p.40

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestCandidate
import Definitions.Def_ReservationPolicy_IsPolicyEq
import Definitions.Def_ReservationPolicy_welfare
import Definitions.Def_ReservationPolicy_Params_dX
import Definitions.Def_ReservationPolicy_Params_dY

namespace ReservationPolicy

/-- **Equation (55).** Overall welfare at an equilibrium under a transfer of `s` seats is the printed
expression in the cutoffs (51)–(52), and that expression is a concave quadratic in `s`. Bao, Ni &
Singh, SSRN 3772113 (May 30, 2023), eq. (55), p.40 (PDF 40). -/
theorem eq_55 (P : Params) (hP : P.Valid) (b : Benchmark) (hb : IsInvestCandidate P b) :
    ∃ a c₁ c₀ : ℝ, a < 0 ∧ ∀ (s : ℝ) (o : PolicyOutcome), IsPolicyEq P b s o →
      welfare P o =
        P.α * (1 / 4 * (1 - P.dX s + (1 + P.dX s) / (8 * P.k - 1)) *
              (1 + P.dX s + (1 + P.dX s) / (8 * P.k - 1)) -
            P.k * ((1 + P.dX s) / (8 * P.k - 1)) ^ 2 - P.κ) +
          (1 - P.α) * (1 / 4 * (1 - P.dY s + P.ϕ ^ 2 * (1 + P.dY s) / (8 * P.k - P.ϕ ^ 2)) *
              (1 + P.dY s + P.ϕ ^ 2 * (1 + P.dY s) / (8 * P.k - P.ϕ ^ 2)) -
            P.k * (P.ϕ * (1 + P.dY s) / (8 * P.k - P.ϕ ^ 2)) ^ 2) ∧
      welfare P o = a * s ^ 2 + c₁ * s + c₀ := by sorry

end ReservationPolicy
