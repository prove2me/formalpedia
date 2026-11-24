-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_pow
-- name    : ReciprocityTheory.ChartRestriction.L1.integralMv_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:20.550863+00:00
-- url     : https://prove2.me/theorems/6d95e0bd-713d-471a-a253-2eeaec52f856
-- title:
--   L1: integral Mv pow
-- statement:
--   The L1 construction uses the integral Mv pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L104-L107

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

theorem ReciprocityTheory.ChartRestriction.L1.integralMv_pow {F : MvPowerSeries ι K} (hF : IntegralMv F) (n : ℕ) : IntegralMv (F ^ n) := by sorry
