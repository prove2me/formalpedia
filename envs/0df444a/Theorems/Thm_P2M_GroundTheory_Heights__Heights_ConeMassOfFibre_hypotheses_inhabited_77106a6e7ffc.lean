-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_hypotheses_inhabited_77106a6e7ffc
-- name    : P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_hypotheses_inhabited_77106a6e7ffc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:20.389453+00:00
-- url     : https://prove2.me/theorems/09f9c2d1-f92d-426f-9d19-593f12aa0bbc
-- title:
--   P2 M Ground Theory Heights  Heights Cone Mass Of Fibre hypotheses inhabited 77106a6e7ffc: P2 M Ground Theory Heights  Heights Cone Mass Of Fibre hypotheses inhabited 77106a6e7ffc
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Mass Of Fibre hypotheses inhabited 77106a6e7ffc construction uses the P2 M Ground Theory Heights  Heights Cone Mass Of Fibre hypotheses inhabited 77106a6e7ffc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeMass.lean#L20-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeMass.lean#L20-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreDegree_hypotheses_inhabited_7d66142c3999
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerMul_hypotheses_inhabited_95e2ae5d82a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinear_hypotheses_inhabited_1fdf021d66be

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
open MvPolynomial MeasureTheory
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_hypotheses_inhabited_77106a6e7ffc :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      ∀ᵐ π : Fin 1 → Fin 1 → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 1),
        fibreCount (HermNorm.std 1) ⊥ π w = ((1 : ℕ) : ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMassOfFibre».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_hypotheses_inhabited_77106a6e7ffc
