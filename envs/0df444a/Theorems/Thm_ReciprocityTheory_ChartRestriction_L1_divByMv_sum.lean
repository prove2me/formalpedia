-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_sum
-- name    : ReciprocityTheory.ChartRestriction.L1.divByMv_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:44:52.014674+00:00
-- url     : https://prove2.me/theorems/967b7ece-45bf-42f9-bef6-9b4697bc618a
-- title:
--   L1: div By Mv sum
-- statement:
--   The L1 construction uses the div By Mv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L81-L83

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

theorem ReciprocityTheory.ChartRestriction.L1.divByMv_sum {x : K} {α : Type} (s : Finset α) (F : α → MvPowerSeries ι K)
    (hF : ∀ i ∈ s, DivByMv x (F i)) : DivByMv x (∑ i ∈ s, F i) := by sorry
