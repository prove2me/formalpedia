-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_shape
-- name    : ReciprocityTheory.ChartRestriction.L1.rmu_shape
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:46:33.498846+00:00
-- url     : https://prove2.me/theorems/74d592c3-ea6c-4906-b0b1-2cc7d01db3a1
-- title:
--   L1: rmu shape
-- statement:
--   The L1 construction uses the rmu shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsPowerMulUnitNorm.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsPowerMulUnitNorm.lean#L77-L84

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

theorem ReciprocityTheory.ChartRestriction.L1.rmu_shape {a : ℂ_[l]} (ha : a ∈ Rmu l) (ha0 : a ≠ 0) :
    ∃ m : ℕ, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by sorry
