-- Prove2me | Theorems.Thm_SystemicDiv_SellOff_proposition_4_4
-- name    : SystemicDiv.SellOff.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:21.789779+00:00
-- url     : https://prove2.me/theorems/0491eae1-a853-48ea-a82c-2dfa56b893ba
-- title:
--   Proposition 4.4, p. 20 — equilibrium portfolios overlap less than single-bank optima: $|\pi^*_{1,1}-\pi^*_{2,1}| > |\pi^S_{1,1}-\pi^S_{2,1}|$
-- statement:
--   Let $N = K = 2$ and $0 < \gamma_1 < \gamma_2$, with a shock law satisfying Assumption 3.3 and $E\|Z\|^2 < \infty$, and fix $w_1, w_2, \lambda_{M,1}, \lambda_{M,2}$. There is $\bar\ell > 0$ (Assumption 3.7) such that the following holds. Let the two banks satisfy the standing assumptions with $\ell_1 < \ell_2 \le \bar\ell$. Assume the potential is strictly convex on $\Pi^2$ (Assumption 3.6) and each $S_i$ is convex on $\Pi$. Let $\pi^*$ be a Nash equilibrium, and $\pi^S_i$ bank $i$'s single-bank optimal portfolio. Then
--   $$|\pi^*_{1,1} - \pi^*_{2,1}| > |\pi^S_{1,1} - \pi^S_{2,1}|.$$
--
--   Accounting for each other's liquidations, heterogeneous banks move their portfolios apart: this is **systemic diversification**.
--
--   **Formalization Note.** Bank $1$ and asset $1$ are index `0`. Added: $E\|Z\|^2 < \infty$, and the convexity of each $S_i$ (the hypothesis of Proposition 4.2, which the proof invokes). $\bar\ell$ depends on $\mu, \gamma, w, \lambda_M$ but not on the leverages. The statement holds for every Nash equilibrium and every choice of single-bank optima.
-- source:
--   Capponi & Weber, Systemic Portfolio Diversification, SSRN 3345399 (version of June 15, 2023), p. 20, Proposition 4.4; proof pp. 45–47

import Mathlib
import Definitions.Def_SystemicDiv_SellOff_Model

open MeasureTheory

namespace SystemicDiv.SellOff

/-- Proposition 4.4, p. 20 (`N = K = 2`, `γ_1 < γ_2`, `ℓ_1 < ℓ_2`, Assumptions 3.3, 3.6, 3.7):
`|π*_{1,1} − π*_{2,1}| > |π^S_{1,1} − π^S_{2,1}|`. Bank 1 and asset 1 are index `0`. -/
theorem proposition_4_4 (μ : Measure (Shock 2)) [IsProbabilityMeasure μ]
    (hZ : Assumption33 μ) (hM2 : SecondMoment μ)
    (γ : Fin 2 → ℝ) (hγ : 0 < γ 0 ∧ γ 0 < γ 1) (w levM : Fin 2 → ℝ) :
    ∃ ellbar > 0, ∀ lev0 lev1 : ℝ,
      let B : Fin 2 → Bank := ![⟨w 0, lev0, levM 0⟩, ⟨w 1, lev1, levM 1⟩]
      (∀ i, (B i).Standing) → (B 0).ell < (B 1).ell → (B 1).ell ≤ ellbar →
      StrictConvexOn ℝ (Admissible 2 2) (Pot μ B γ) →
      (∀ i, ConvexOn ℝ (stdSimplex ℝ (Fin 2)) (S μ γ (B i))) →
      ∀ piStar : Fin 2 → Fin 2 → ℝ, IsNash μ B γ piStar →
      ∀ piS : Fin 2 → Fin 2 → ℝ, (∀ i, IsBenchmark μ γ (B i) (piS i)) →
        |piS 0 0 - piS 1 0| < |piStar 0 0 - piStar 1 0| := by sorry

end SystemicDiv.SellOff
