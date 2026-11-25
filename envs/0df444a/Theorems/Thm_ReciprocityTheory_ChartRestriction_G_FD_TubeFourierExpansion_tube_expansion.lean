-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TubeFourierExpansion_tube_expansion
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.tube_expansion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:06.568421+00:00
-- url     : https://prove2.me/theorems/125e5e2c-2e29-43ea-9d2a-c9c14b9938dc
-- title:
--   Tube Fourier Expansion: tube expansion
-- statement:
--   The Tube Fourier Expansion construction uses the tube expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeFourierExpansion.lean#L68-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeFourierExpansion.lean#L68-L257

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeSummability
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeFourierExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
open Complex MeasureTheory Metric ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.tube_expansion (Ω : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (hΩ : IsOpen Ω)
    (hc : Convex ℝ Ω) (h0 : (0 : Fin n → ℝ) ∈ Ω) (hd : DifferentiableOn ℂ h (tube n Ω))
    (hp : ∀ s ∈ tube n Ω, ∀ m : Fin n → ℤ, h (s + fun k => (m k : ℂ)) = h s)
    (u : Fin n → ℂ) (hu : u ∈ tube n Ω) :
    Summable (fun k : Fin n → ℤ =>
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖) ∧
    HasSum (fun k : Fin n → ℤ => fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j))
      (h u) := by sorry
