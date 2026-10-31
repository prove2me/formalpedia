-- Prove2me | Theorems.Thm_ReservationPolicy_eq_56
-- name    : ReservationPolicy.eq_56
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:26.552762+00:00
-- url     : https://prove2.me/theorems/fdbdab7b-e0c3-42de-9a6d-7c94a272f740
-- title:
--   Equation (56) — the vertex of welfare (corrected: $\mu_2$)
-- statement:
--   Let the parameters satisfy the standing assumptions. Then $\mu_2>0$, and there are $c>0$ and $U_0$ with
--   $$
--   U=U_0-c\,\Bigl(s-\frac{(4k-1)(1-\alpha)\alpha(4k-\phi^2)(1-\phi^2)\mu_1}{(8k-1)(8k-\phi^2)\mu_2}\Bigr)^2
--   $$
--   at every equilibrium under a transfer of $s$ seats. So (56) is the unique solution of the first-order condition.
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - correction: d ∈ (0,1), said to be equivalent to 4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2 (p.9) → the z-interval alone, with no bound on d (Params.Valid); reason: the two are not equivalent: k = 1, ϕ = 1/2, α = 1/2, z = 7/100 is in the interval with d* = 3427/3300 > 1; the interval is what the proof of Proposition 1 uses (p.35) and contains the region d* ∈ (0,1)
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
--   - correction: μ₂ with first term 16k(16k² − 3k − 5kα) + α → first term 16k(16k² − 3k − 5kα + α); reason: a misplaced bracket: at k = 1, ϕ = 1/2, α = 3/10, z = 2/5 the maximizer is 63/32786, and the printed μ₂ gives 1953/989326
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (56) and $\mu_2 > 0$, pp.40–41

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestCandidate
import Definitions.Def_ReservationPolicy_IsPolicyEq
import Definitions.Def_ReservationPolicy_welfare
import Definitions.Def_ReservationPolicy_Params_sVertex

namespace ReservationPolicy

/-- **Equation (56).** `μ₂ > 0`, and `U` is a downward parabola in `s` with vertex (56). Bao, Ni & Singh,
SSRN 3772113 (May 30, 2023), eq. (56), pp.40–41 (PDF 40–41), with `μ₂` corrected. -/
theorem eq_56 (P : Params) (hP : P.Valid) (b : Benchmark) (hb : IsInvestCandidate P b) :
    0 < P.mu2 ∧ ∃ c U₀ : ℝ, 0 < c ∧ ∀ (s : ℝ) (o : PolicyOutcome), IsPolicyEq P b s o →
      welfare P o = U₀ - c * (s - P.sVertex) ^ 2 := by sorry

end ReservationPolicy
