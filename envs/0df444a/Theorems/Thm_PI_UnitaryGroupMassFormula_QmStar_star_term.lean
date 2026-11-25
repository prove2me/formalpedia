-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_star_term
-- name    : PI.UnitaryGroupMassFormula.QmStar.star_term
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:35:55.664241+00:00
-- url     : https://prove2.me/theorems/c57849a6-6383-5289-9eef-4a804b925885
-- title:
--   Qm Star: star term
-- statement:
--   The Qm Star construction uses the star term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L77-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerProductCast/OfFnProdIntCast.lean#L77-L90

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

theorem PI.UnitaryGroupMassFormula.QmStar.star_term {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (ε : Fin n → ℤˣ)
    (hs : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (a b : Fin t → Fin n) (w : ℂ)
    (σ : Equiv.Perm (Fin t)) :
    star ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun k : Fin t => Tm E (w - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).prod) =
      ((((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) : A) * ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun j : Fin t =>
          Tm E (star w - (t : ℂ) + 1 + ((j : ℕ) : ℂ)) (b j.rev) (a (σ j.rev))).prod) := by sorry
