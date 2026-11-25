-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneMass_of_fibre_zero_5619f5cadf5c
-- name    : P2M_GroundTheory_Heights__Heights_coneMass_of_fibre_zero_5619f5cadf5c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:44:36.305492+00:00
-- url     : https://prove2.me/theorems/f086651f-b324-4372-be44-56d8b897af85
-- title:
--   P2 M Ground Theory Heights  Heights cone Mass of fibre zero 5619f5cadf5c: P2 M Ground Theory Heights  Heights cone Mass of fibre zero 5619f5cadf5c
-- statement:
--   The P2 M Ground Theory Heights  Heights cone Mass of fibre zero 5619f5cadf5c construction uses the P2 M Ground Theory Heights  Heights cone Mass of fibre zero 5619f5cadf5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L215-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L215-L277

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_coneMass_of_fibre_zero_5619f5cadf5c {n δ : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : IsProjPrime J)
    (hfib : ∀ᵐ π : Fin 0 → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 0), fibreCount h J π w = δ) :
    Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} =
      (δ : ℝ≥0∞) * Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, 0 ≤ (j : ℕ) → y j = 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coneMass_of_fibre_zero» := P2M_GroundTheory_Heights__Heights_coneMass_of_fibre_zero_5619f5cadf5c
