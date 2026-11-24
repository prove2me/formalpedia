-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_int_unit
-- name    : ReciprocityTheory.ChartRestriction.L1.kq_int_unit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:24.688863+00:00
-- url     : https://prove2.me/theorems/2278e3cf-9608-4211-b410-db800e677aad
-- title:
--   L1: kq int unit
-- statement:
--   The L1 construction uses the kq int unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormSqrtNegPowPrimeSqSub.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormSqrtNegPowPrimeSqSub.lean#L39-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormSqrtNegPowPrimeSqSub
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

theorem ReciprocityTheory.ChartRestriction.L1.kq_int_unit (n : ℤ) (h : ¬ (l : ℤ) ∣ n) : ‖(n : ℂ_[l])‖ = 1 := by sorry
