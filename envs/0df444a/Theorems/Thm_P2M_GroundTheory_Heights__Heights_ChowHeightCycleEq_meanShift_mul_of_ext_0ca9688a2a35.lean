-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_of_ext_0ca9688a2a35
-- name    : P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_of_ext_0ca9688a2a35
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:36.363799+00:00
-- url     : https://prove2.me/theorems/ed77a55e-3d5a-4068-b0f6-b3050edc3ace
-- title:
--   P2 M Ground Theory Heights  Heights Chow Height Cycle Eq mean Shift mul of ext 0ca9688a2a35: P2 M Ground Theory Heights  Heights Chow Height Cycle Eq mean Shift mul of ext 0ca9688a2a35
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Height Cycle Eq mean Shift mul of ext 0ca9688a2a35 construction uses the P2 M Ground Theory Heights  Heights Chow Height Cycle Eq mean Shift mul of ext 0ca9688a2a35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L143-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L143-L216

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

theorem P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_of_ext_0ca9688a2a35 (hA : ChowHeightMul.Statement) {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] (j : K →+* L) (τ : L →+* ℂ) (hτ : ¬ ComplexEmbedding.IsReal τ)
    (σ : K →+* ℂ) (hσ : ComplexEmbedding.IsReal σ) (hτj : τ.comp j = σ)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (hf : f ≠ 0) (hg : g ≠ 0) :
    meanShift S σ (f * g) = meanShift S σ f + meanShift S σ g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowHeightCycleEq».«meanShift_mul_of_ext» := P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_of_ext_0ca9688a2a35
