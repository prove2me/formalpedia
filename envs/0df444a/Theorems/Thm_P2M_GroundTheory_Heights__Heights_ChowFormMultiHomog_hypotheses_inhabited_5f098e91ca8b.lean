-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormMultiHomog_hypotheses_inhabited_5f098e91ca8b
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormMultiHomog_hypotheses_inhabited_5f098e91ca8b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:21:03.323868+00:00
-- url     : https://prove2.me/theorems/cb4946d0-346e-5867-85d5-7eacd6a2c2fc
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Multi Homog hypotheses inhabited 5f098e91ca8b: P2 M Ground Theory Heights  Heights Chow Form Multi Homog hypotheses inhabited 5f098e91ca8b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Multi Homog hypotheses inhabited 5f098e91ca8b construction uses the P2 M Ground Theory Heights  Heights Chow Form Multi Homog hypotheses inhabited 5f098e91ca8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Statements.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Statements.lean#L118-L121

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ChowFormMultiHomog_hypotheses_inhabited_5f098e91ca8b :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 (X (0, 0)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormMultiHomog».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ChowFormMultiHomog_hypotheses_inhabited_5f098e91ca8b
