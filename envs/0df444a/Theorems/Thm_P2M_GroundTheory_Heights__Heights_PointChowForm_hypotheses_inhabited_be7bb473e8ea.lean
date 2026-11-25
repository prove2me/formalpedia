-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointChowForm_hypotheses_inhabited_be7bb473e8ea
-- name    : P2M_GroundTheory_Heights__Heights_PointChowForm_hypotheses_inhabited_be7bb473e8ea
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:15.776551+00:00
-- url     : https://prove2.me/theorems/b64661b5-74f6-4016-9d15-7dc296d68c14
-- title:
--   P2 M Ground Theory Heights  Heights Point Chow Form hypotheses inhabited be7bb473e8ea: P2 M Ground Theory Heights  Heights Point Chow Form hypotheses inhabited be7bb473e8ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Chow Form hypotheses inhabited be7bb473e8ea construction uses the P2 M Ground Theory Heights  Heights Point Chow Form hypotheses inhabited be7bb473e8ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L371-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L371-L375

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormBaseChange_hypotheses_inhabited_d4e9bb785044
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralMass_hypotheses_inhabited_a1fb323fc42c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GreenSymmetry_hypotheses_inhabited_2fbf7471ddd6
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointChowForm_hypotheses_inhabited_be7bb473e8ea :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 (X (0, 0)) ∧ (fun _ : Fin 1 => (1 : ℂ)) ≠ 0 ∧
      ∀ x : Fin 1 → ℂ, (∀ q ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)), eval x q = 0) ↔
        ∃ t : ℂ, x = t • (fun _ => (1 : ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointChowForm».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_PointChowForm_hypotheses_inhabited_be7bb473e8ea
