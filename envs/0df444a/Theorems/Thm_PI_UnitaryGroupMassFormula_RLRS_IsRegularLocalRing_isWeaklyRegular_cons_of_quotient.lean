-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_RLRS_IsRegularLocalRing_isWeaklyRegular_cons_of_quotient
-- name    : PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isWeaklyRegular_cons_of_quotient
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:32:42.10995+00:00
-- url     : https://prove2.me/theorems/05fc3e6a-b5ec-52df-86cd-18bd0cef12c3
-- title:
--   Is Regular Local Ring: is Weakly Regular cons of quotient
-- statement:
--   The Is Regular Local Ring construction uses the is Weakly Regular cons of quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RegularLocalRegularSequence/ExistsIsRegularOfListEqMaximalIdeal.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RegularLocalRegularSequence/ExistsIsRegularOfListEqMaximalIdeal.lean#L14-L29

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

theorem PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isWeaklyRegular_cons_of_quotient {A : Type u} [CommRing A] {x : A}
    (hx : IsSMulRegular A x) (ys : List A)
    (hys : IsWeaklyRegular (A ⧸ Ideal.span ({x} : Set A))
      (ys.map (Ideal.Quotient.mk (Ideal.span ({x} : Set A))))) :
    IsWeaklyRegular A (x :: ys) := by sorry
