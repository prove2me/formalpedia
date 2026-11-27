-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_RLRS_IsRegularLocalRing_exists_isRegular_ofList_eq_maximalIdeal
-- name    : PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:48:06.727698+00:00
-- url     : https://prove2.me/theorems/79972785-4db5-4044-95a7-82362be77acf
-- title:
--   Is Regular Local Ring: exists is Regular of List eq maximal Ideal
-- statement:
--   The Is Regular Local Ring construction uses the exists is Regular of List eq maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RegularLocalRegularSequence/ExistsIsRegularOfListEqMaximalIdeal.lean#L96-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RegularLocalRegularSequence/ExistsIsRegularOfListEqMaximalIdeal.lean#L96-L107

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

theorem PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal (A : Type u) [CommRing A]
    [IsRegularLocalRing A] :
    ∃ xs : List A, Ideal.ofList xs = maximalIdeal A ∧
      (xs.length : WithBot ℕ∞) = ringKrullDim A ∧ IsRegular A xs := by sorry
