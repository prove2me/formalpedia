-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TubeFourierExpansion_abs_sign_le
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.abs_sign_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:23.562588+00:00
-- url     : https://prove2.me/theorems/f6b55ce2-c34d-4d5e-b3d0-ccf6039b33e6
-- title:
--   Tube Fourier Expansion: abs sign le
-- statement:
--   The Tube Fourier Expansion construction uses the abs sign le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeFourierExpansion.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeFourierExpansion.lean#L57-L58

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

theorem ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.abs_sign_le (a : ℤ) : |(a.sign : ℝ)| ≤ 1 := by sorry
