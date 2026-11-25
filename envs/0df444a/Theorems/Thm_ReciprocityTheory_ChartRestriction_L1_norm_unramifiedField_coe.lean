-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_unramifiedField_coe
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_unramifiedField_coe
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:44.61982+00:00
-- url     : https://prove2.me/theorems/1fb6bce8-f674-5231-89be-4c9bdbd2e36c
-- title:
--   L1: norm unramified Field coe
-- statement:
--   The L1 construction uses the norm unramified Field coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsExtendEndomorphismFractions.lean#L142-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsExtendEndomorphismFractions.lean#L142-L142

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
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

theorem ReciprocityTheory.ChartRestriction.L1.norm_unramifiedField_coe (x : Kmu l) : ‖x‖ = ‖(x : ℂ_[l])‖ := by sorry
