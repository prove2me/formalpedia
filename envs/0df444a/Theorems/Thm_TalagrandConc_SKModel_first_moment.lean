-- Prove2me | Theorems.Thm_TalagrandConc_SKModel_first_moment
-- name    : TalagrandConc.SKModel.first_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:20.802981+00:00
-- url     : https://prove2.me/theorems/bea426b2-eb65-4298-9e24-f13ba6198009
-- title:
--   Equation (12.7) — first moment of Z_N
-- statement:
--   There is an absolute $K>0$ such that, for every $N\ge1$, $0<\beta\le1$, and independent interaction couplings with common centered, unit-variance law $\nu$, zero third moment, and the chapter's exponential moment assumptions, $Z_N$ is integrable and
--
--   $$K^{-1}e^{\beta^2N/4}\le\mathbb E Z_N\le K e^{\beta^2N/4}.$$
--
--   This estimate compares the annealed partition function with its high-temperature scale. Integrability is asserted explicitly so the expectation has its ordinary mathematical meaning.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), pp. 193–195, Eq. (12.7)

import Mathlib
import Definitions.Def_TalagrandConc_SKModel_Basic

namespace TalagrandConc.SKModel

/-- Talagrand (12.7), p. 193. -/
theorem first_moment :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (ν : MeasureTheory.Measure ℝ)
      [MeasureTheory.IsProbabilityMeasure ν] (β : ℝ),
      1 ≤ N → 0 < β → β ≤ 1 → AdmissibleLaw ν → LightTails ν →
      MeasureTheory.Integrable (partitionFunction N β) (couplingLaw N ν) ∧
      K⁻¹ * Real.exp (β ^ 2 * N / 4) ≤
        ∫ h, partitionFunction N β h ∂(couplingLaw N ν) ∧
      (∫ h, partitionFunction N β h ∂(couplingLaw N ν)) ≤
        K * Real.exp (β ^ 2 * N / 4) := by sorry

end TalagrandConc.SKModel
