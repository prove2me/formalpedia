-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_derivative
-- name    : ReciprocityTheory.ChartRestriction.L1.integralPS_derivative
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:47.741179+00:00
-- url     : https://prove2.me/theorems/439d62a3-8628-556f-8264-e3bf255b3a8d
-- title:
--   L1: integral PS derivative
-- statement:
--   The L1 construction uses the integral PS derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L169-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L169-L172

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

theorem ReciprocityTheory.ChartRestriction.L1.integralPS_derivative {f : PowerSeries K} (hf : IntegralPS f) :
    IntegralPS (derivative K f) := by sorry
