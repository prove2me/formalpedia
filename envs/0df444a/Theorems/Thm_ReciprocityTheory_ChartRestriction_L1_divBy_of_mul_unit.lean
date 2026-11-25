-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_of_mul_unit
-- name    : ReciprocityTheory.ChartRestriction.L1.divBy_of_mul_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:45:04.988856+00:00
-- url     : https://prove2.me/theorems/e1b54f3e-2772-5b35-b0e5-3dd61bc080f6
-- title:
--   L1: div By of mul unit
-- statement:
--   The L1 construction uses the div By of mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L194-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L194-L202

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

theorem ReciprocityTheory.ChartRestriction.L1.divBy_of_mul_unit {x : K} {f g : PowerSeries K} (hf : IntegralPS f)
    (h0 : ‖constantCoeff f‖ = 1) (h : DivBy x (f * g)) : DivBy x g := by sorry
