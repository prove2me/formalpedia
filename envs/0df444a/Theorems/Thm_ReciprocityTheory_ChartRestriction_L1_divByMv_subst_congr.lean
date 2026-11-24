-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_subst_congr
-- name    : ReciprocityTheory.ChartRestriction.L1.divByMv_subst_congr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:44:54.162746+00:00
-- url     : https://prove2.me/theorems/3ccfcb2a-f344-4b45-bcf1-96190b14c95e
-- title:
--   L1: div By Mv subst congr
-- statement:
--   The L1 construction uses the div By Mv subst congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L301-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L301-L335

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

theorem ReciprocityTheory.ChartRestriction.L1.divByMv_subst_congr {x : K} (hx : ‖x‖ ≤ 1) {f : PowerSeries K} {P Q : MvPowerSeries ι K}
    (hf : IntegralPS f) (hP0 : MvPowerSeries.constantCoeff P = 0)
    (hQ0 : MvPowerSeries.constantCoeff Q = 0) (hP : IntegralMv P) (hQ : IntegralMv Q)
    (hPQ : DivByMv x (P - Q)) : DivByMv x (f.subst P - f.subst Q) := by sorry
