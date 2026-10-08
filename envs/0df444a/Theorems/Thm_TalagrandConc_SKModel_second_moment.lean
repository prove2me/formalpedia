-- Prove2me | Theorems.Thm_TalagrandConc_SKModel_second_moment
-- name    : TalagrandConc.SKModel.second_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:15.941172+00:00
-- url     : https://prove2.me/theorems/def6c92c-d468-4d3e-8301-5be692644097
-- title:
--   Equation (12.8) — second moment of Z_N
-- statement:
--   There is an absolute $K>0$ such that, for every $N\ge8$, $0<\beta<1$, and independent interaction couplings with common centered, unit-variance law $\nu$, zero third moment, and the chapter's exponential moment assumptions, both $Z_N$ and $Z_N^2$ are integrable and
--
--   $$\mathbb E Z_N^2\le\frac{K}{1-\beta^2}(\mathbb E Z_N)^2.$$
--
--   This estimate controls the probability that the partition function is substantially smaller than its mean. The $N\ge8$ range is the range of the second-moment calculation on p. 195; smaller sizes would require stronger exponential moments for $Z_N^2$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), pp. 193 and 195, Eq. (12.8)

import Mathlib
import Definitions.Def_TalagrandConc_SKModel_Basic

namespace TalagrandConc.SKModel

/-- Talagrand (12.8), pp. 193 and 195. -/
theorem second_moment :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (ν : MeasureTheory.Measure ℝ)
      [MeasureTheory.IsProbabilityMeasure ν] (β : ℝ),
      8 ≤ N → 0 < β → β < 1 → AdmissibleLaw ν → LightTails ν →
      MeasureTheory.Integrable (partitionFunction N β) (couplingLaw N ν) ∧
      MeasureTheory.Integrable (fun h => partitionFunction N β h ^ 2) (couplingLaw N ν) ∧
      (∫ h, partitionFunction N β h ^ 2 ∂(couplingLaw N ν)) ≤
        K / (1 - β ^ 2) *
          (∫ h, partitionFunction N β h ∂(couplingLaw N ν)) ^ 2 := by sorry

end TalagrandConc.SKModel
