-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_int_dvd
-- name    : ReciprocityTheory.ChartRestriction.L1.kq_int_dvd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:19.979433+00:00
-- url     : https://prove2.me/theorems/826b2cdb-4bc1-5cb9-bf7c-ac53d3fab79f
-- title:
--   L1: kq int dvd
-- statement:
--   The L1 construction uses the kq int dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormSqrtNegPowPrimeSqSub.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormSqrtNegPowPrimeSqSub.lean#L33-L37

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

theorem ReciprocityTheory.ChartRestriction.L1.kq_int_dvd (n : ℤ) (h : (l : ℤ) ∣ n) : ‖(n : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by sorry
