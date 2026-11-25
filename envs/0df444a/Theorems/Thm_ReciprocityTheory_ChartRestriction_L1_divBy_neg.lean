-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_neg
-- name    : ReciprocityTheory.ChartRestriction.L1.divBy_neg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:44:10.782678+00:00
-- url     : https://prove2.me/theorems/fc53be3f-2752-41fa-9305-b65a54f52f4f
-- title:
--   L1: div By neg
-- statement:
--   The L1 construction uses the div By neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L132-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L132-L133

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

theorem ReciprocityTheory.ChartRestriction.L1.divBy_neg {x : K} {f : PowerSeries K} (hf : DivBy x f) : DivBy x (-f) := by sorry
