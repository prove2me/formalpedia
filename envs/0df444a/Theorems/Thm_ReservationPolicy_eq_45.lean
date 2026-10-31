-- Prove2me | Theorems.Thm_ReservationPolicy_eq_45
-- name    : ReservationPolicy.eq_45
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:25:58.591469+00:00
-- url     : https://prove2.me/theorems/54b2d133-e106-4f13-9d8a-d0cbeffb0fbf
-- title:
--   Equation (45) — condition for a no-investment equilibrium (corrected: effort and $z$ domains)
-- statement:
--   Let the parameters satisfy the standing assumptions and
--   $$
--   \hat{\hat\kappa}=\frac{k(1-z)^2(1-\phi^2)}{(4k-\phi^2)^2}.
--   $$
--   Then $\hat{\hat\kappa}<\kappa^*$, a benchmark equilibrium in which type $x$ does not invest exists if and only if $\kappa\ge\hat{\hat\kappa}$, and in every such equilibrium all students exert effort $e^*=\phi(1-z)/(4k-\phi^2)$ and are admitted with probability $\rho^*=z$, so that $EI=0$.
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - correction: d ∈ (0,1), said to be equivalent to 4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2 (p.9) → the z-interval alone, with no bound on d (Params.Valid); reason: the two are not equivalent: k = 1, ϕ = 1/2, α = 1/2, z = 7/100 is in the interval with d* = 3427/3300 > 1; the interval is what the proof of Proposition 1 uses (p.35) and contains the region d* ∈ (0,1)
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
--   - reading: κ > κ̂̂, strict → κ̂̂ ≤ κ; reason: footnote 22 sets the knife edge aside; at equality the pure equilibrium exists with weak best responses
--   - generalization: κ > κ̂̂ derived as a necessary condition → an equivalence with existence; reason: the candidate of (38)–(40) is an equilibrium whenever the deviation is not profitable
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (39), (40), (45), pp.36–37

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsNoInvestBenchmark
import Definitions.Def_ReservationPolicy_Params_kappaStar
import Definitions.Def_ReservationPolicy_Params_kappaDoubleHat

namespace ReservationPolicy

/-- **Equation (45), with (39)–(40).** An equilibrium without investment exists exactly when `κ` is at
least the double-hat threshold, which lies below `κ*`; in it both types exert effort
`ϕ(1−z)/(4k−ϕ²)` and are admitted with probability `z`. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023),
eqs. (39), (40), (45), pp.36–37 (PDF 36–37). -/
theorem eq_45 (P : Params) (hP : P.Valid) :
    P.kappaDoubleHat < P.kappaStar ∧
    ((∃ b, IsNoInvestBenchmark P b) ↔ P.kappaDoubleHat ≤ P.κ) ∧
    ∀ b, IsNoInvestBenchmark P b →
      b.ex = P.ϕ * (1 - P.z) / (4 * P.k - P.ϕ ^ 2) ∧
      b.ey = P.ϕ * (1 - P.z) / (4 * P.k - P.ϕ ^ 2) ∧
      admitProb (P.ϕ * b.ex) b.d = P.z ∧ admitProb (P.ϕ * b.ey) b.d = P.z := by sorry

end ReservationPolicy
