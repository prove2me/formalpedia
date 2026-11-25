-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_exp_nine_quarters_lt
-- name    : ReciprocityTheory.ChartRestriction.G.FD.exp_nine_quarters_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:39.366356+00:00
-- url     : https://prove2.me/theorems/bdeaa732-3187-592b-8424-606d53daf10e
-- title:
--   FD: exp nine quarters lt
-- statement:
--   The FD construction uses the exp nine quarters lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SchwarzLemmaBallHolds.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SchwarzLemmaBallHolds.lean#L7-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SchwarzLemmaBallHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Metric Set

theorem ReciprocityTheory.ChartRestriction.G.FD.exp_nine_quarters_lt : Real.exp (9 / 4) < 9.5 := by sorry
