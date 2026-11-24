-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_subst
-- name    : ReciprocityTheory.ChartRestriction.L1.divByMv_subst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:44:24.487954+00:00
-- url     : https://prove2.me/theorems/468b0058-5749-425f-af03-3894117a0492
-- title:
--   L1: div By Mv subst
-- statement:
--   The L1 construction uses the div By Mv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L284-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L284-L299

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

theorem ReciprocityTheory.ChartRestriction.L1.divByMv_subst {x : K} {f : PowerSeries K} {P : MvPowerSeries ι K} (hf : DivBy x f)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) : DivByMv x (f.subst P) := by sorry
