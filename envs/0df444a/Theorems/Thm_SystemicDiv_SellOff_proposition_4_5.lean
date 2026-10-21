-- Prove2me | Theorems.Thm_SystemicDiv_SellOff_proposition_4_5
-- name    : SystemicDiv.SellOff.proposition_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:24.459281+00:00
-- url     : https://prove2.me/theorems/c2296c5a-c394-4d25-b2a9-fedeec00317a
-- title:
--   Proposition 4.5, p. 24 — in equilibrium P(some bank liquidates) rises and P(both liquidate) falls relative to the single-bank benchmark
-- statement:
--   Let $N = K = 2$ and $0 < \gamma_1 < \gamma_2$, with a shock law satisfying Assumption 3.3 and $E\|Z\|^2 < \infty$, and fix $w_1, w_2, \lambda_{M,1}, \lambda_{M,2}$. There is $\bar\ell > 0$ (Assumption 3.7) with the following property. For every leverage $\lambda_1$ of bank 1 meeting the standing assumptions there is $\delta > 0$ such that, for every leverage $\lambda_2$ of bank 2 meeting them with
--   $$\ell_1 < \ell_2 \le \bar\ell, \qquad \ell_2 < \ell_1 + \delta,$$
--   if the potential is strictly convex on $\Pi^2$ (Assumption 3.6) and each $S_i$ is convex on $\Pi$, then every Nash equilibrium $\pi^*$ and every choice of single-bank optima $\pi^S_1, \pi^S_2$ satisfy
--   $$P\big(A_{liq}(\pi^*_1,\pi^*_2)\big) > P\big(A_{liq}(\pi^S_1,\pi^S_2)\big) \quad\text{and}\quad P\big(A_{sim}(\pi^*_1,\pi^*_2)\big) < P\big(A_{sim}(\pi^S_1,\pi^S_2)\big).$$
--   Here $A_{liq}$ is the event that at least one bank liquidates and $A_{sim}$ the event that both do.
--
--   Systemic diversification has a cost and a benefit. In equilibrium, liquidation by at least one bank becomes more likely, while simultaneous liquidation becomes less likely, compared with banks that ignore each other.
--
--   **Formalization Note.** Bank $1$ and asset $1$ are index `0`. Added, all drawn from the proof on p. 47:
--   1. Assumption 3.6 and the convexity of each $S_i$ (the proof relies on Propositions 4.2 and 4.4, which assume them);
--   2. the closeness $\ell_2 < \ell_1 + \delta$ (the proof uses "$\ell_1$ and $\ell_2$ are sufficiently close" to place the holdings in $[\tfrac12, \tfrac{\gamma_2}{\gamma_1+\gamma_2}]$);
--   3. $E\|Z\|^2 < \infty$.
--
--   $\bar\ell$ depends on $\mu, \gamma, w, \lambda_M$ only; $\delta$ may also depend on $\lambda_1$. Probabilities are `μ.real` of the liquidation events, defined by the model's strict leverage rule.
-- source:
--   Capponi & Weber, Systemic Portfolio Diversification, SSRN 3345399 (version of June 15, 2023), p. 24, Proposition 4.5; proof pp. 47–48

import Mathlib
import Definitions.Def_SystemicDiv_SellOff_Model

open MeasureTheory

namespace SystemicDiv.SellOff

/-- Proposition 4.5, p. 24 (`N = K = 2`, `γ_1 < γ_2`, `ℓ_1 < ℓ_2`, Assumptions 3.3 and 3.7):
`P(A_liq(π*_1, π*_2)) > P(A_liq(π^S_1, π^S_2))` and `P(A_sim(π*_1, π*_2)) < P(A_sim(π^S_1, π^S_2))`.
Added, as in the proof (p. 47): Assumption 3.6, convexity of each `S_i`, and `ℓ_1`, `ℓ_2`
sufficiently close (`ℓ_2 < ℓ_1 + δ`). Bank 1 and asset 1 are index `0`. -/
theorem proposition_4_5 (μ : Measure (Shock 2)) [IsProbabilityMeasure μ]
    (hZ : Assumption33 μ) (hM2 : SecondMoment μ)
    (γ : Fin 2 → ℝ) (hγ : 0 < γ 0 ∧ γ 0 < γ 1) (w levM : Fin 2 → ℝ) :
    ∃ ellbar > 0, ∀ lev0 : ℝ, (⟨w 0, lev0, levM 0⟩ : Bank).Standing →
      ∃ δ > 0, ∀ lev1 : ℝ,
        let B : Fin 2 → Bank := ![⟨w 0, lev0, levM 0⟩, ⟨w 1, lev1, levM 1⟩]
        (B 1).Standing → (B 0).ell < (B 1).ell → (B 1).ell ≤ ellbar →
        (B 1).ell < (B 0).ell + δ →
        StrictConvexOn ℝ (Admissible 2 2) (Pot μ B γ) →
        (∀ i, ConvexOn ℝ (stdSimplex ℝ (Fin 2)) (S μ γ (B i))) →
        ∀ piStar : Fin 2 → Fin 2 → ℝ, IsNash μ B γ piStar →
        ∀ piS : Fin 2 → Fin 2 → ℝ, (∀ i, IsBenchmark μ γ (B i) (piS i)) →
          μ.real (Aliq B piS) < μ.real (Aliq B piStar) ∧
            μ.real (Asim B piStar) < μ.real (Asim B piS) := by sorry

end SystemicDiv.SellOff
