-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_subst2
-- name    : ReciprocityTheory.ChartRestriction.L1.integralMv_subst2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:04.06536+00:00
-- url     : https://prove2.me/theorems/96a6eace-6965-4529-99ec-e48f1c303afe
-- title:
--   L1: integral Mv subst2
-- statement:
--   The L1 construction uses the integral Mv subst2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L357-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L357-L361

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

theorem ReciprocityTheory.ChartRestriction.L1.integralMv_subst2 {F : MvPowerSeries (Fin 2) K} {P : Fin 2 → MvPowerSeries ι K}
    (hF : IntegralMv F) (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv (P i)) : IntegralMv (F.subst P) := by sorry
