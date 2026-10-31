-- Prove2me | Theorems.Thm_ReservationPolicy_eq_28
-- name    : ReservationPolicy.eq_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:09.513994+00:00
-- url     : https://prove2.me/theorems/dea88ac3-8f17-4760-8777-1404843c4f73
-- title:
--   Equation (28) — equilibrium admission probabilities (corrected: effort and $z$ domains)
-- statement:
--   Let the parameters satisfy the standing assumptions, and write $\Gamma=32k^2+\phi^2-4k[1+2\phi^2+\alpha(1-\phi^2)]$. The quantities
--   $$
--   \rho_x^*=\frac{32k^2z+z\phi^2+4k(1-\alpha)(1-\phi^2)-4kz(2+\phi^2)}{\Gamma},\qquad
--   \rho_y^*=\frac{32k^2z+z\phi^2-4k(z+\alpha+2z\phi^2-\alpha\phi^2)}{\Gamma}
--   $$
--   satisfy $0<\rho_y^*<\rho_x^*<1$, and they are the admission probabilities at every effort-stage outcome with type $x$ investing. The lower bound on $z$ in the standing assumptions is exactly $\rho_y^*>0$.
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - correction: d ∈ (0,1), said to be equivalent to 4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2 (p.9) → the z-interval alone, with no bound on d (Params.Valid); reason: the two are not equivalent: k = 1, ϕ = 1/2, α = 1/2, z = 7/100 is in the interval with d* = 3427/3300 > 1; the interval is what the proof of Proposition 1 uses (p.35) and contains the region d* ∈ (0,1)
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
--   - generalization: ρ* bounded between 0 and 1 → also ρ*_y < ρ*_x; reason: the page's (47) gives it, and EI > 0 is used in the proof of Proposition 6
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (28), p.35

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestCandidate
import Definitions.Def_ReservationPolicy_Params_rhoXStar
import Definitions.Def_ReservationPolicy_Params_rhoYStar

namespace ReservationPolicy

/-- **Equation (28).** The closed forms of `ρ*` lie strictly between `0` and `1`, type `x` above type
`y`, and every effort-stage outcome with type `x` investing has them as its admission probabilities.
Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eq. (28), p.35 (PDF 35). -/
theorem eq_28 (P : Params) (hP : P.Valid) :
    0 < P.rhoYStar ∧ P.rhoYStar < P.rhoXStar ∧ P.rhoXStar < 1 ∧
    ∀ b, IsInvestCandidate P b → b.rhoX = P.rhoXStar ∧ b.rhoY P = P.rhoYStar := by sorry

end ReservationPolicy
