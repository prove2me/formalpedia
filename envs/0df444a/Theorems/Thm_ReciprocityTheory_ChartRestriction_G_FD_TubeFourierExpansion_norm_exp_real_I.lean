-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TubeFourierExpansion_norm_exp_real_I
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.norm_exp_real_I
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:25.503719+00:00
-- url     : https://prove2.me/theorems/539433cf-dc9f-44ba-a2e3-c4707f0308c7
-- title:
--   Tube Fourier Expansion: norm exp real I
-- statement:
--   The Tube Fourier Expansion construction uses the norm exp real I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeFourierExpansion.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeFourierExpansion.lean#L60-L66

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

theorem ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.norm_exp_real_I (c : ℝ) (k : Fin n → ℤ) (x0 : Fin n → ℝ) :
    ‖cexp (c * I * ∑ j, (k j : ℂ) * (x0 j : ℂ))‖ = 1 := by sorry
