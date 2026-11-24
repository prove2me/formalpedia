-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsHalfReps_injOn
-- name    : ReciprocityTheory.ChartRestriction.L1.IsHalfReps.injOn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:55:41.044011+00:00
-- url     : https://prove2.me/theorems/be4839b9-9bab-494c-98a1-71293ba0f5ab
-- title:
--   Is Half Reps: inj On
-- statement:
--   The Is Half Reps construction uses the inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedHalf.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedHalf.lean#L69-L71

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

theorem ReciprocityTheory.ChartRestriction.L1.IsHalfReps.injOn (h : IsHalfReps L α T) : Set.InjOn L.weierstrassP (T : Set ℂ) := by sorry
