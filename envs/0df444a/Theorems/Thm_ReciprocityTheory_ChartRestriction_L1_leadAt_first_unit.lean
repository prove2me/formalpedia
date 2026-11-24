-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_leadAt_first_unit
-- name    : ReciprocityTheory.ChartRestriction.L1.leadAt_first_unit
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:11.078546+00:00
-- url     : https://prove2.me/theorems/d6d6ce25-4fca-40c5-b9fe-4de5a343a26d
-- title:
--   L1: lead At first unit
-- statement:
--   The L1 construction uses the lead At first unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgGauss.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgGauss.lean#L134-L138

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgGauss
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
open Formalism.L2.Th1
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem ReciprocityTheory.ChartRestriction.L1.leadAt_first_unit {g : PowerSeries K} (hg : IntegralPS g) (h : ∃ i, ‖coeff i g‖ = 1) :
    ∃ i₀, (∀ i, ‖coeff i g‖ = 1 → i₀ ≤ i) ∧ LeadAt g 1 i₀ := by sorry
