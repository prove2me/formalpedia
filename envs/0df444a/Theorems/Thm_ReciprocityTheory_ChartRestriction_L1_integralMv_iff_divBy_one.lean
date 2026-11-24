-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one
-- name    : ReciprocityTheory.ChartRestriction.L1.integralMv_iff_divBy_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:16.482144+00:00
-- url     : https://prove2.me/theorems/eaa57fb2-5979-4471-a980-f5efaa21842a
-- title:
--   L1: integral Mv iff div By one
-- statement:
--   The L1 construction uses the integral Mv iff div By one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L15-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {ι : Type}

theorem ReciprocityTheory.ChartRestriction.L1.integralMv_iff_divBy_one (F : MvPowerSeries ι K) : IntegralMv F ↔ DivByMv (1 : K) F := by sorry
