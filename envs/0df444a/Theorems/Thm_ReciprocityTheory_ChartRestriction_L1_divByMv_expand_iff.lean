-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_expand_iff
-- name    : ReciprocityTheory.ChartRestriction.L1.divByMv_expand_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:01.890802+00:00
-- url     : https://prove2.me/theorems/5fcb5640-b40b-4dc5-b1a0-9134b208a102
-- title:
--   L1: div By Mv expand iff
-- statement:
--   The L1 construction uses the div By Mv expand iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L235-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L235-L252

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

theorem ReciprocityTheory.ChartRestriction.L1.divByMv_expand_iff {ι : Type} (x : K) (n : ℕ) (hn : n ≠ 0) (F : MvPowerSeries ι K) :
    DivByMv x (MvPowerSeries.expand n hn F) ↔ DivByMv x F := by sorry
