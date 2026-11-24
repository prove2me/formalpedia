-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kur_discrete
-- name    : ReciprocityTheory.ChartRestriction.L1.kur_discrete
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:38:29.158684+00:00
-- url     : https://prove2.me/theorems/233a6823-943f-4d97-ac5d-10046595192b
-- title:
--   L1: kur discrete
-- statement:
--   The L1 construction uses the kur discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsTeichmullerRepModPrime.lean#L125-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsTeichmullerRepModPrime.lean#L125-L133

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

theorem ReciprocityTheory.ChartRestriction.L1.kur_discrete {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by sorry
