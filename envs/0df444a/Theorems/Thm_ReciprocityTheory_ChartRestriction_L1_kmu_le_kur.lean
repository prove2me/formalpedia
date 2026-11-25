-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmu_le_kur
-- name    : ReciprocityTheory.ChartRestriction.L1.kmu_le_kur
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:12.162296+00:00
-- url     : https://prove2.me/theorems/ab2a0ffe-1acc-54ea-a336-99937618b498
-- title:
--   L1: kmu le kur
-- statement:
--   The L1 construction uses the kmu le kur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsTeichmullerRepModPrime.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsTeichmullerRepModPrime.lean#L19-L19

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

theorem ReciprocityTheory.ChartRestriction.L1.kmu_le_kur {x : ℂ_[l]} (hx : x ∈ Kmu l) : x ∈ MaximalUnramifiedExtension l := by sorry
