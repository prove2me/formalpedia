-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_conv_of_hasSum
-- name    : ReciprocityTheory.ChartRestriction.L1.conv_of_hasSum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:43:42.675356+00:00
-- url     : https://prove2.me/theorems/a36b16a9-2e33-498d-95a5-c9c5199e6df2
-- title:
--   L1: conv of has Sum
-- statement:
--   The L1 construction uses the conv of has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L22-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L22-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.conv_of_hasSum {f : PowerSeries ℂ}
    (h : ∀ x : ℂ, ‖x‖ < 1 → Summable fun n => PowerSeries.coeff n f * x ^ n) : Conv f := by sorry
