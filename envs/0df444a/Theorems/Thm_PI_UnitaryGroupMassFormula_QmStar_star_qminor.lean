-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_star_qminor
-- name    : PI.UnitaryGroupMassFormula.QmStar.star_qminor
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:08.031315+00:00
-- url     : https://prove2.me/theorems/e7454d5c-67a1-5dfa-ba0f-32bf01e0db20
-- title:
--   Qm Star: star qminor
-- statement:
--   The Qm Star construction uses the star qminor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L92-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L92-L107

import Definitions.Def_Formalism_PeriodIntegrals_QmStar
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmStar

theorem PI.UnitaryGroupMassFormula.QmStar.star_qminor {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (ε : Fin n → ℤˣ)
    (hs : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (a b : Fin t → Fin n) (w : ℂ) :
    star (qminor E a b w) = ((((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) : A) *
      PI.qminorRow E (b ∘ Fin.rev) (a ∘ Fin.rev) (star w) := by sorry
