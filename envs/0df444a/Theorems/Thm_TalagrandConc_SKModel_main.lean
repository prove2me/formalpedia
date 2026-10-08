-- Prove2me | Theorems.Thm_TalagrandConc_SKModel_main
-- name    : TalagrandConc.SKModel.main
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:25.916473+00:00
-- url     : https://prove2.me/theorems/fa5cfa97-8e91-46bc-8d7f-bdb4a7e6d52b
-- title:
--   Theorem 12.1 — high-temperature deviations of log Z_N
-- statement:
--   There is one absolute constant $K>0$ with the following property. For every $N\ge1$, $0<\beta<1$, and i.i.d. interaction couplings with common law $\nu$, assume mean and third moment zero, second moment one, a finite exponential moment of $|h|$ near the origin, and $\mathbb E e^h<2$ and $\mathbb E e^{-h}<2$. Then $F_N=\log Z_N$ is integrable and, whenever $0<t<N/K$,
--
--   $$P_N\!\left(\left|F_N-\frac{\beta^2N}{4}\right|\ge K\left(t+\sqrt{\log\frac{K}{1-\beta^2}}\right)\sqrt N\right)\le2e^{-t^2}.$$
--
--   The same $K$ also gives
--
--   $$-\frac K{\sqrt N}\sqrt{\log\frac2{1-\beta^2}}\le\frac1N\mathbb E F_N-\frac{\beta^2}4\le\frac KN.$$
--
--   The theorem locates the random free energy around the high-temperature value and bounds its expected value per site. The universal constant is chosen before $N$, $\beta$, $\nu$, and $t$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 192, Theorem 12.1, Eqs. (12.3)–(12.4)

import Mathlib
import Definitions.Def_TalagrandConc_SKModel_Basic

namespace TalagrandConc.SKModel

/-- Talagrand Theorem 12.1, (12.3) and (12.4), p. 192. -/
theorem main :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (ν : MeasureTheory.Measure ℝ)
      [MeasureTheory.IsProbabilityMeasure ν] (β : ℝ),
      1 ≤ N → 0 < β → β < 1 → AdmissibleLaw ν → LightTails ν →
      MeasureTheory.Integrable (freeEnergy N β) (couplingLaw N ν) ∧
      (∀ t : ℝ, 0 < t → t < N / K →
        (couplingLaw N ν {h |
          K * (t + Real.sqrt (Real.log (K / (1 - β ^ 2)))) * Real.sqrt N ≤
            |freeEnergy N β h - β ^ 2 * N / 4|}).toReal ≤
          2 * Real.exp (-(t ^ 2))) ∧
      -(K / Real.sqrt N) * Real.sqrt (Real.log (2 / (1 - β ^ 2))) ≤
        (∫ h, freeEnergy N β h ∂(couplingLaw N ν)) / N - β ^ 2 / 4 ∧
      (∫ h, freeEnergy N β h ∂(couplingLaw N ν)) / N - β ^ 2 / 4 ≤
        K / N := by sorry

end TalagrandConc.SKModel
