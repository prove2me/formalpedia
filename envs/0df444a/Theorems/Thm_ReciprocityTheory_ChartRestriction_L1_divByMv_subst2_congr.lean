-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_subst2_congr
-- name    : ReciprocityTheory.ChartRestriction.L1.divByMv_subst2_congr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:55.054018+00:00
-- url     : https://prove2.me/theorems/91d77615-2a68-4cfa-b886-4de11afe992a
-- title:
--   L1: div By Mv subst2 congr
-- statement:
--   The L1 construction uses the div By Mv subst2 congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L362-L404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L362-L404

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

theorem ReciprocityTheory.ChartRestriction.L1.divByMv_subst2_congr {x : K} (hx : ‖x‖ ≤ 1) {F : MvPowerSeries (Fin 2) K}
    {P Q : Fin 2 → MvPowerSeries ι K} (hF : IntegralMv F)
    (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hQ0 : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) (hP : ∀ i, IntegralMv (P i))
    (hQ : ∀ i, IntegralMv (Q i)) (hPQ : ∀ i, DivByMv x (P i - Q i)) :
    DivByMv x (F.subst P - F.subst Q) := by sorry
