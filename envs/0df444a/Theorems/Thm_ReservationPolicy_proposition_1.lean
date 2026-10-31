-- Prove2me | Theorems.Thm_ReservationPolicy_proposition_1
-- name    : ReservationPolicy.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:32.628721+00:00
-- url     : https://prove2.me/theorems/c16607d3-42e0-420f-b4c2-332304a04f2e
-- title:
--   Proposition 1 — equilibrium investment and effort (corrected: effort and $z$ domains)
-- statement:
--   Let the parameters satisfy the standing assumptions and let $\kappa<\hat\kappa=\min\{\hat{\hat\kappa},\tilde\kappa\}$. Then an equilibrium exists, every equilibrium has type-$x$ students investing $\kappa$, and with $\Delta=(8k-\phi^2)(8k-1-\alpha)-\phi^2(1-\alpha)(8k-1)$ the efforts are
--   $$
--   e_x^*=\frac{2(1-z)(8k-\phi^2)}{\Delta},\qquad e_y^*=\frac{2(1-z)(8k-1)\phi}{\Delta}.
--   $$
--   This is the paper's description of who invests and how hard each type studies; it is the base of the policy analysis.
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - correction: d ∈ (0,1), said to be equivalent to 4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2 (p.9) → the z-interval alone, with no bound on d (Params.Valid); reason: the two are not equivalent: k = 1, ϕ = 1/2, α = 1/2, z = 7/100 is in the interval with d* = 3427/3300 > 1; the interval is what the proof of Proposition 1 uses (p.35) and contains the region d* ∈ (0,1)
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
--   - generalization: the efforts in equilibrium → existence of an equilibrium as well; reason: the page presupposes it; the proof constructs it
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), Proposition 1, p.13, with κ̂ of p.37

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestBenchmark
import Definitions.Def_ReservationPolicy_IsNoInvestBenchmark
import Definitions.Def_ReservationPolicy_Params_kappaHat

namespace ReservationPolicy

/-- **Proposition 1.** If `κ < κ̂`, an equilibrium exists, no equilibrium has type `x` not investing,
and the efforts of every equilibrium are (14). Bao, Ni & Singh, SSRN 3772113 (May 30, 2023),
Proposition 1, p.13 (PDF 13), with `κ̂` of p.37.

**Formalization Note** Footnote 14 applies payoff dominance when two equilibria coexist. It is not
needed under `κ < κ̂`, because `κ̂ ≤ κ̂̂` and no no-investment equilibrium exists below `κ̂̂`. -/
theorem proposition_1 (P : Params) (hP : P.Valid) (hκ : P.κ < P.kappaHat) :
    (∃ b, IsInvestBenchmark P b) ∧
    (∀ b, ¬ IsNoInvestBenchmark P b) ∧
    ∀ b, IsInvestBenchmark P b →
      b.ex = 2 * (1 - P.z) * (8 * P.k - P.ϕ ^ 2) /
        ((8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1)) ∧
      b.ey = 2 * (1 - P.z) * (8 * P.k - 1) * P.ϕ /
        ((8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1)) := by sorry

end ReservationPolicy
