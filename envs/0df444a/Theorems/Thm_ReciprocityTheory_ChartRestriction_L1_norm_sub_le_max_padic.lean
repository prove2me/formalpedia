-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_sub_le_max_padic
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_sub_le_max_padic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:24.917799+00:00
-- url     : https://prove2.me/theorems/e95fdfd6-6fa5-44ce-8d12-02256325dc9b
-- title:
--   L1: norm sub le max padic
-- statement:
--   The L1 construction uses the norm sub le max padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsTeichmullerRepModPrime.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsTeichmullerRepModPrime.lean#L26-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
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
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.norm_sub_le_max_padic (x y : ℂ_[l]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by sorry
