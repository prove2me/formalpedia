-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_lintegral_matGauss_of_ae_eq_09c348418b22
-- name    : P2M_GroundTheory_Heights__Heights_lintegral_matGauss_of_ae_eq_09c348418b22
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:48:22.749558+00:00
-- url     : https://prove2.me/theorems/e777cff9-d8ac-444c-ac0d-adcfc9a83469
-- title:
--   P2 M Ground Theory Heights  Heights lintegral mat Gauss of ae eq 09c348418b22: P2 M Ground Theory Heights  Heights lintegral mat Gauss of ae eq 09c348418b22
-- statement:
--   The P2 M Ground Theory Heights  Heights lintegral mat Gauss of ae eq 09c348418b22 construction uses the P2 M Ground Theory Heights  Heights lintegral mat Gauss of ae eq 09c348418b22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L196-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L196-L213

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

theorem P2M_GroundTheory_Heights__Heights_lintegral_matGauss_of_ae_eq_09c348418b22 {m n : ℕ} (c : ℕ)
    (N : (Fin m → Fin n → ℂ) → EuclideanSpace ℂ (Fin m) → ℕ∞)
    (hN : ∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), N π w = c) :
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (N π w : ℝ≥0∞) =
      (c : ℝ≥0∞) * ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«lintegral_matGauss_of_ae_eq» := P2M_GroundTheory_Heights__Heights_lintegral_matGauss_of_ae_eq_09c348418b22
