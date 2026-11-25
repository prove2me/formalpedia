-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_star_Tm
-- name    : PI.UnitaryGroupMassFormula.QmStar.star_Tm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:12.154548+00:00
-- url     : https://prove2.me/theorems/98ba8e9f-447c-5a73-abb1-c327c5ab236e
-- title:
--   Qm Star: star Tm
-- statement:
--   The Qm Star construction uses the star Tm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L31-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L31-L42

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

theorem PI.UnitaryGroupMassFormula.QmStar.star_Tm {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (ε : Fin n → ℤˣ)
    (hs : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (u : ℂ) (c d : Fin n) :
    star (Tm E u c d) = (((ε c * ε d : ℤˣ) : ℤ) : A) * Tm E (star u) d c := by sorry
