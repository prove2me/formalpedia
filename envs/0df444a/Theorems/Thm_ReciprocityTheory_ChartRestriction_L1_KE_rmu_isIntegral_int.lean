-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_rmu_isIntegral_int
-- name    : ReciprocityTheory.ChartRestriction.L1.KE.rmu_isIntegral_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:43:15.258073+00:00
-- url     : https://prove2.me/theorems/f0d8cd2c-d1de-4b04-86ce-7a17b04125be
-- title:
--   KE: rmu is Integral int
-- statement:
--   The KE construction uses the rmu is Integral int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L126-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L126-L135

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

theorem ReciprocityTheory.ChartRestriction.L1.KE.rmu_isIntegral_int {x : ℂ_[l]} (hx : x ∈ Rmu l) : IsIntegral ℤ x := by sorry
