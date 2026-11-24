-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_mul
-- name    : ReciprocityTheory.ChartRestriction.L1.divByMv_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:44:35.073717+00:00
-- url     : https://prove2.me/theorems/2bac40d7-1fcd-40ef-9a23-285d1b342529
-- title:
--   L1: div By Mv mul
-- statement:
--   The L1 construction uses the div By Mv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L66-L76

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

theorem ReciprocityTheory.ChartRestriction.L1.divByMv_mul {x y : K} {F G : MvPowerSeries ι K} (hF : DivByMv x F) (hG : DivByMv y G) :
    DivByMv (x * y) (F * G) := by sorry
