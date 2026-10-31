-- Prove2me | Theorems.Thm_ReservationPolicy_eq_32
-- name    : ReservationPolicy.eq_32
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:14.24106+00:00
-- url     : https://prove2.me/theorems/27672533-faa3-4790-9408-82a218bb4977
-- title:
--   Equation (32) — no profitable deviation from investing (corrected: effort and $z$ domains)
-- statement:
--   Let the parameters satisfy the standing assumptions and let $b$ be an effort-stage outcome with type $x$ investing. Then
--
--   1. if $\kappa\le\kappa^*$, no type-$x$ student gains by not investing;
--   2. if the deviation effort $e^{dev}=\phi r_x/(4k)$ of (31) is admissible and no type-$x$ student gains by not investing, then $\kappa\le\kappa^*$;
--   3. $e^{dev}$ is admissible whenever $d<1$.
--
--   Here
--   $$
--   \kappa^*=\frac{k(1-z)^2(1-\phi^2)(8k-\phi^2)^2}{\bigl(\phi^2+4k(8k-1-\alpha-(2-\alpha)\phi^2)\bigr)^2}.
--   $$
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - correction: d ∈ (0,1), said to be equivalent to 4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2 (p.9) → the z-interval alone, with no bound on d (Params.Valid); reason: the two are not equivalent: k = 1, ϕ = 1/2, α = 1/2, z = 7/100 is in the interval with d* = 3427/3300 > 1; the interval is what the proof of Proposition 1 uses (p.35) and contains the region d* ∈ (0,1)
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
--   - reading: κ < κ*, strict → κ ≤ κ*; reason: at equality a type-x student is indifferent, the knife edge of footnote 22, and a pure equilibrium still exists
--   - reading: the deviation (30)–(31) is always available → clause 2 assumes (31) is admissible, and clause 3 shows it is when d < 1; reason: with d > 1 the first-order deviation can have ρ ≤ 0, where (30) is not a probability
--   - generalization: κ < κ* derived as a necessary condition → sufficiency in clause 1 as well; reason: the proof's comparison gives both directions
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (30)–(32), pp.35–36

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestCandidate
import Definitions.Def_ReservationPolicy_InvestOptimal
import Definitions.Def_ReservationPolicy_Params_kappaStar

namespace ReservationPolicy

/-- **Equation (32).** Investing is not deviated from when `κ ≤ κ*`. Conversely, if the deviation
effort (31) is an admissible effort, which holds whenever `d < 1`, then `κ ≤ κ*` is necessary.
Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eqs. (30)–(32), pp.35–36 (PDF 35–36). -/
theorem eq_32 (P : Params) (hP : P.Valid) (b : Benchmark) (hb : IsInvestCandidate P b) :
    (P.κ ≤ P.kappaStar → InvestOptimal P b.d b.rx b.ex) ∧
    (P.ϕ * b.rx / (4 * P.k) ∈ plainEfforts P b.d →
      InvestOptimal P b.d b.rx b.ex → P.κ ≤ P.kappaStar) ∧
    (b.d < 1 → P.ϕ * b.rx / (4 * P.k) ∈ plainEfforts P b.d) := by sorry

end ReservationPolicy
