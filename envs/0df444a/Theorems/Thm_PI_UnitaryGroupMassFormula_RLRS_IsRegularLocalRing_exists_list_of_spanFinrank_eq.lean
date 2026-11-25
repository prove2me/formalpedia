-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_RLRS_IsRegularLocalRing_exists_list_of_spanFinrank_eq
-- name    : PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_list_of_spanFinrank_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:32:57.862336+00:00
-- url     : https://prove2.me/theorems/bf1c4767-79db-4877-a2ea-4405274c048f
-- title:
--   Is Regular Local Ring: exists list of span Finrank eq
-- statement:
--   The Is Regular Local Ring construction uses the exists list of span Finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RegularLocalRegularSequence/ExistsIsRegularOfListEqMaximalIdeal.lean#L31-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RegularLocalRegularSequence/ExistsIsRegularOfListEqMaximalIdeal.lean#L31-L94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_ExistsIsRegularOfListEqMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.RLRS
open PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
open IsLocalRing RingTheory.Sequence
open scoped Pointwise
universe u

theorem PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_list_of_spanFinrank_eq :
    ∀ (n : ℕ) (A : Type u) [CommRing A] [IsRegularLocalRing A],
      Submodule.spanFinrank (maximalIdeal A) = n →
      ∃ xs : List A, Ideal.ofList xs = maximalIdeal A ∧ xs.length = n ∧
        IsWeaklyRegular A xs := by sorry
