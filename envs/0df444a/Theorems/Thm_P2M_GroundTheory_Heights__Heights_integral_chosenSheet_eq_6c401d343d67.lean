-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_chosenSheet_eq_6c401d343d67
-- name    : P2M_GroundTheory_Heights__Heights_integral_chosenSheet_eq_6c401d343d67
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:04.30489+00:00
-- url     : https://prove2.me/theorems/13e8b779-e822-464c-9504-f97e2a1d8f02
-- title:
--   P2 M Ground Theory Heights  Heights integral chosen Sheet eq 6c401d343d67: P2 M Ground Theory Heights  Heights integral chosen Sheet eq 6c401d343d67
-- statement:
--   The P2 M Ground Theory Heights  Heights integral chosen Sheet eq 6c401d343d67 construction uses the P2 M Ground Theory Heights  Heights integral chosen Sheet eq 6c401d343d67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeChartArea.lean#L56-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeChartArea.lean#L56-L139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre mcPts)

theorem P2M_GroundTheory_Heights__Heights_integral_chosenSheet_eq_6c401d343d67 {n e : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (P : Ideal (MRing (PBlk n))) (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (g : (Fin n → ℂ) → ℝ) (hg : ∀ (c : ℂ) (z : Fin n → ℂ), c ≠ 0 → g (c • z) = g z)
    (x : Fin e → ℂ) (w : ((k : Unit) → PBlk n k) → ℂ) :
    ∫ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y))
          (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
        (‖t‖ ^ (2 * e) * gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) * chartGramDensity P Ψ S g x w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«integral_chosenSheet_eq» := P2M_GroundTheory_Heights__Heights_integral_chosenSheet_eq_6c401d343d67
