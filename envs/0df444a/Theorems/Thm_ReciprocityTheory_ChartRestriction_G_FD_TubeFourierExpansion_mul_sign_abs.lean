-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TubeFourierExpansion_mul_sign_abs
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.mul_sign_abs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:23.741864+00:00
-- url     : https://prove2.me/theorems/f8744346-56a4-4759-94c9-c426e3ba86ae
-- title:
--   Tube Fourier Expansion: mul sign abs
-- statement:
--   The Tube Fourier Expansion construction uses the mul sign abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeFourierExpansion.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeFourierExpansion.lean#L47-L55

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

theorem ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.mul_sign_abs (a : ℤ) : (a : ℝ) * (a.sign : ℝ) = |(a : ℝ)| := by sorry
