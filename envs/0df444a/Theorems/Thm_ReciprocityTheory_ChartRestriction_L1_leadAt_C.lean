-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_leadAt_C
-- name    : ReciprocityTheory.ChartRestriction.L1.leadAt_C
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:15.185503+00:00
-- url     : https://prove2.me/theorems/03ba5b37-e0c1-4cc3-872c-d5d90199bfea
-- title:
--   L1: lead At C
-- statement:
--   The L1 construction uses the lead At C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgGauss.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgGauss.lean#L66-L69

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

theorem ReciprocityTheory.ChartRestriction.L1.leadAt_C {c : K} (hc : c ≠ 0) : LeadAt (C c : PowerSeries K) ‖c‖ 0 := by sorry
