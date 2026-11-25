-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_d1c5c8b18f4b
-- name    : P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_d1c5c8b18f4b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:48.70852+00:00
-- url     : https://prove2.me/theorems/bec021b6-e845-4320-a1b4-67fb66b7bbb9
-- title:
--   P2 M Ground Theory Heights  Heights Chow Height Cycle Eq mean Shift mul d1c5c8b18f4b: P2 M Ground Theory Heights  Heights Chow Height Cycle Eq mean Shift mul d1c5c8b18f4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Height Cycle Eq mean Shift mul d1c5c8b18f4b construction uses the P2 M Ground Theory Heights  Heights Chow Height Cycle Eq mean Shift mul d1c5c8b18f4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L218-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L218-L258

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_d1c5c8b18f4b (hA : ChowHeightMul.Statement) {K : Type} [Field K] [NumberField K]
    (σ : K →+* ℂ) (hσ : ComplexEmbedding.IsReal σ)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (hf : f ≠ 0) (hg : g ≠ 0) :
    meanShift S σ (f * g) = meanShift S σ f + meanShift S σ g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowHeightCycleEq».«meanShift_mul» := P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_d1c5c8b18f4b
