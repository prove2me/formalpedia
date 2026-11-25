-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_power_mul_unitNorm
-- name    : ReciprocityTheory.ChartRestriction.L1.exists_power_mul_unitNorm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:43:27.155971+00:00
-- url     : https://prove2.me/theorems/bf7fafc4-922f-4cfd-81e1-5b55e5a86287
-- title:
--   L1: exists power mul unit Norm
-- statement:
--   The L1 construction uses the exists power mul unit Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsPowerMulUnitNorm.lean#L33-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsPowerMulUnitNorm.lean#L33-L75

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

theorem ReciprocityTheory.ChartRestriction.L1.exists_power_mul_unitNorm (k : ℕ) : ∀ a ∈ Rmu l, a ≠ 0 → 1 < (l : ℝ) ^ k * ‖a‖ →
    ∃ m : ℕ, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by sorry
