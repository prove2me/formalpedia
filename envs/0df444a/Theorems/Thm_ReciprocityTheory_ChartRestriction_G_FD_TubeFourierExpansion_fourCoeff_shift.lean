-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TubeFourierExpansion_fourCoeff_shift
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.fourCoeff_shift
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:28.309521+00:00
-- url     : https://prove2.me/theorems/53b86837-83a2-537b-bfcb-f6c8e28117ea
-- title:
--   Tube Fourier Expansion: four Coeff shift
-- statement:
--   The Tube Fourier Expansion construction uses the four Coeff shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeFourierExpansion.lean#L9-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeFourierExpansion.lean#L9-L45

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

theorem ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.fourCoeff_shift (g : (Fin n → ℂ) → ℂ) (y0 : Fin n → ℝ) (k : Fin n → ℤ) :
    fourCoeff (fun t => g (t + fun j => (y0 j : ℂ) * I)) 0 k =
      (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) * fourCoeff g y0 k := by sorry
