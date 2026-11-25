-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_tch_mem_rmu
-- name    : ReciprocityTheory.ChartRestriction.L1.KE.tch_mem_rmu
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:49:28.367117+00:00
-- url     : https://prove2.me/theorems/e76baf32-9759-5391-abcd-4271637325d6
-- title:
--   KE: tch mem rmu
-- statement:
--   The KE construction uses the tch mem rmu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L145-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L145-L148

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1 ReciprocityTheory.ChartRestriction.L1.KE
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.KE.tch_mem_rmu {x : ℂ_[l]} (hx : x ∈ Tch l) : x ∈ Rmu l := by sorry
