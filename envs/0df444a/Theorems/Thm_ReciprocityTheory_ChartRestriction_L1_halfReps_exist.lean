-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_halfReps_exist
-- name    : ReciprocityTheory.ChartRestriction.L1.halfReps_exist
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:44.405053+00:00
-- url     : https://prove2.me/theorems/cbfc9f52-5028-462a-9e7a-0d278541f365
-- title:
--   L1: half Reps exist
-- statement:
--   The L1 construction uses the half Reps exist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedHalf.lean#L107-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedHalf.lean#L107-L139

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

theorem ReciprocityTheory.ChartRestriction.L1.halfReps_exist (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (hs : MulStable L α) (N : ℕ)
    (hN : Complex.normSq α = N) (hodd : Odd N) : ∃ T : Finset ℂ, IsHalfReps L α T := by sorry
