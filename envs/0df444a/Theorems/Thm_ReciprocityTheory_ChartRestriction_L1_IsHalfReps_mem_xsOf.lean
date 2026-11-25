-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsHalfReps_mem_xsOf
-- name    : ReciprocityTheory.ChartRestriction.L1.IsHalfReps.mem_xsOf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:44:43.597003+00:00
-- url     : https://prove2.me/theorems/62d1d8e0-e3a1-583e-b160-317a069faf5c
-- title:
--   Is Half Reps: mem xs Of
-- statement:
--   The Is Half Reps construction uses the mem xs Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedHalf.lean#L83-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedHalf.lean#L83-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {L : PeriodPair} {α : ℂ} {T : Finset ℂ}

theorem ReciprocityTheory.ChartRestriction.L1.IsHalfReps.mem_xsOf (h : IsHalfReps L α T) (hs : MulStable L α) {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassP z ∈ xsOf L T ↔ α * z ∈ L.lattice := by sorry
