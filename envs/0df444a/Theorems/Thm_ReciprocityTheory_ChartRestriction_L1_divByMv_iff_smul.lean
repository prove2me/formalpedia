-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_iff_smul
-- name    : ReciprocityTheory.ChartRestriction.L1.divByMv_iff_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:16.327011+00:00
-- url     : https://prove2.me/theorems/093689af-ba22-588c-a06e-0e0fcc6d6711
-- title:
--   L1: div By Mv iff smul
-- statement:
--   The L1 construction uses the div By Mv iff smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L109-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L109-L123

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

theorem ReciprocityTheory.ChartRestriction.L1.divByMv_iff_smul {x : K} (hx : x ≠ 0) (F : MvPowerSeries ι K) :
    DivByMv x F ↔ ∃ G : MvPowerSeries ι K, IntegralMv G ∧ F = x • G := by sorry
