-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_iff_mv
-- name    : ReciprocityTheory.ChartRestriction.L1.integralPS_iff_mv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:28.06285+00:00
-- url     : https://prove2.me/theorems/58c8b8f4-0ffa-4faa-896f-812817d255a1
-- title:
--   L1: integral PS iff mv
-- statement:
--   The L1 construction uses the integral PS iff mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L20-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L20-L34

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

theorem ReciprocityTheory.ChartRestriction.L1.integralPS_iff_mv (f : PowerSeries K) : IntegralPS f ↔ IntegralMv (ι := Unit) f := by sorry
