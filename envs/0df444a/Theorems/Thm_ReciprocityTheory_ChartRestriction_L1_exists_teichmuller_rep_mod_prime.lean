-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_teichmuller_rep_mod_prime
-- name    : ReciprocityTheory.ChartRestriction.L1.exists_teichmuller_rep_mod_prime
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:43:24.761373+00:00
-- url     : https://prove2.me/theorems/1fd04fea-33a5-4e79-8eaa-a04236f8853f
-- title:
--   L1: exists teichmuller rep mod prime
-- statement:
--   The L1 construction uses the exists teichmuller rep mod prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsTeichmullerRepModPrime.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsTeichmullerRepModPrime.lean#L76-L80

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

theorem ReciprocityTheory.ChartRestriction.L1.exists_teichmuller_rep_mod_prime {a : ℂ_[l]} (ha : a ∈ Rmu l) : ∃ ξ ∈ Tch l, ‖a - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by sorry
