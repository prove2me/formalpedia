-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_subst
-- name    : ReciprocityTheory.ChartRestriction.L1.integralMv_subst
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:42:55.727779+00:00
-- url     : https://prove2.me/theorems/3d3aaf7f-32a5-43d0-9561-8c256c00a354
-- title:
--   L1: integral Mv subst
-- statement:
--   The L1 construction uses the integral Mv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L269-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L269-L283

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

theorem ReciprocityTheory.ChartRestriction.L1.integralMv_subst {f : PowerSeries K} {P : MvPowerSeries ι K} (hf : IntegralPS f)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) : IntegralMv (f.subst P) := by sorry
