-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_mul
-- name    : ReciprocityTheory.ChartRestriction.L1.integralMv_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:14.5574+00:00
-- url     : https://prove2.me/theorems/812f978a-edc3-4424-a5a7-53484c5cd3de
-- title:
--   L1: integral Mv mul
-- statement:
--   The L1 construction uses the integral Mv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L99-L103

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

theorem ReciprocityTheory.ChartRestriction.L1.integralMv_mul {F G : MvPowerSeries ι K} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := by sorry
