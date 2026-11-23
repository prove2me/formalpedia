-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_norm_le
-- name    : ReciprocityTheory.ChartRestriction.L1.rmu_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:14.215686+00:00
-- url     : https://prove2.me/theorems/3cce1640-1685-4837-a421-2b5d6d4d432d
-- title:
--   L1: rmu norm le
-- statement:
--   The L1 construction uses the rmu norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsPowerMulUnitNorm.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsPowerMulUnitNorm.lean#L13-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FrobFixNegOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm
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

theorem ReciprocityTheory.ChartRestriction.L1.rmu_norm_le {x : ℂ_[l]} (hx : x ∈ Rmu l) : ‖x‖ ≤ 1 := by sorry
