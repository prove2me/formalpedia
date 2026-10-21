-- Prove2me | Theorems.Thm_SystemicDiv_SellOff_prop_4_5_ordering
-- name    : SystemicDiv.SellOff.prop_4_5_ordering
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:35.564771+00:00
-- url     : https://prove2.me/theorems/21eb9d27-6bdc-4e5f-84f2-61d134a51787
-- title:
--   Proof of Proposition 4.5, p. 47 — $\pi^*_{2,1} < \pi^S_{2,1} < \pi^S_{1,1} < \pi^*_{1,1}$
-- statement:
--   In the setting of Proposition 4.4 ($N = K = 2$, $0 < \gamma_1 < \gamma_2$, Assumption 3.3, $E\|Z\|^2 < \infty$, standing assumptions, $\ell_1 < \ell_2 \le \bar\ell$ for a suitable $\bar\ell > 0$, strict convexity of $P$ on $\Pi^2$, convexity of each $S_i$), every Nash equilibrium $\pi^*$ and every choice of single-bank optima $\pi^S_1, \pi^S_2$ satisfy
--   $$\pi^*_{2,1} < \pi^S_{2,1} < \pi^S_{1,1} < \pi^*_{1,1}.$$
--
--   The more leveraged bank (bank 1) holds more of the liquid asset than the other, and strategic interaction pushes both holdings further apart than in the single-bank benchmark. This ordering is what the proof of Proposition 4.5 uses, and it implies Proposition 4.4.
--
--   **Formalization Note.** Bank $1$ and asset $1$ are index `0`. Hypotheses as in Proposition 4.4.
-- source:
--   Capponi & Weber, Systemic Portfolio Diversification, SSRN 3345399 (version of June 15, 2023), proof of Proposition 4.5, p. 47 (from Propositions 4.2 and 4.4; the ordering is established in the proof of Proposition 4.4, p. 47)

import Mathlib
import Definitions.Def_SystemicDiv_SellOff_Model

open MeasureTheory

namespace SystemicDiv.SellOff

/-- Proof of Proposition 4.5, p. 47: "From Proposition 4.2 and Proposition 4.4 it follows that
`π*_{2,1} < π^S_{2,1} < π^S_{1,1} < π*_{1,1}`" (same setting as Proposition 4.4). Bank 1 and
asset 1 are index `0`. -/
theorem prop_4_5_ordering (μ : Measure (Shock 2)) [IsProbabilityMeasure μ]
    (hZ : Assumption33 μ) (hM2 : SecondMoment μ)
    (γ : Fin 2 → ℝ) (hγ : 0 < γ 0 ∧ γ 0 < γ 1) (w levM : Fin 2 → ℝ) :
    ∃ ellbar > 0, ∀ lev0 lev1 : ℝ,
      let B : Fin 2 → Bank := ![⟨w 0, lev0, levM 0⟩, ⟨w 1, lev1, levM 1⟩]
      (∀ i, (B i).Standing) → (B 0).ell < (B 1).ell → (B 1).ell ≤ ellbar →
      StrictConvexOn ℝ (Admissible 2 2) (Pot μ B γ) →
      (∀ i, ConvexOn ℝ (stdSimplex ℝ (Fin 2)) (S μ γ (B i))) →
      ∀ piStar : Fin 2 → Fin 2 → ℝ, IsNash μ B γ piStar →
      ∀ piS : Fin 2 → Fin 2 → ℝ, (∀ i, IsBenchmark μ γ (B i) (piS i)) →
        piStar 1 0 < piS 1 0 ∧ piS 1 0 < piS 0 0 ∧ piS 0 0 < piStar 0 0 := by sorry

end SystemicDiv.SellOff
