-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_X
-- name    : ReciprocityTheory.ChartRestriction.L1.integralMv_X
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:21.607328+00:00
-- url     : https://prove2.me/theorems/1ff39214-9e43-468e-b67b-054c08890d0c
-- title:
--   L1: integral Mv X
-- statement:
--   The L1 construction uses the integral Mv X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L89-L93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_Formalism_LT_Asm_integralMv_X

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

theorem ReciprocityTheory.ChartRestriction.L1.integralMv_X (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by sorry
