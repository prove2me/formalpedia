-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsHalfReps_card_xsOf
-- name    : ReciprocityTheory.ChartRestriction.L1.IsHalfReps.card_xsOf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:50.405606+00:00
-- url     : https://prove2.me/theorems/e213a10c-c76b-4ede-913f-a1c60e593524
-- title:
--   Is Half Reps: card xs Of
-- statement:
--   The Is Half Reps construction uses the card xs Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedHalf.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedHalf.lean#L73-L74

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

theorem ReciprocityTheory.ChartRestriction.L1.IsHalfReps.card_xsOf (h : IsHalfReps L α T) : (xsOf L T).card = T.card := by sorry
