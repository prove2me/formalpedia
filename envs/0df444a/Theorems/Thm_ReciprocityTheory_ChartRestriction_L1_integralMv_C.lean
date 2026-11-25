-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_C
-- name    : ReciprocityTheory.ChartRestriction.L1.integralMv_C
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:59.482129+00:00
-- url     : https://prove2.me/theorems/3dd4a611-2035-42c8-8065-391e1f2cc87d
-- title:
--   L1: integral Mv C
-- statement:
--   The L1 construction uses the integral Mv C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L94-L98

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

theorem ReciprocityTheory.ChartRestriction.L1.integralMv_C {c : K} (hc : ‖c‖ ≤ 1) : IntegralMv (MvPowerSeries.C c : MvPowerSeries ι K) := by sorry
