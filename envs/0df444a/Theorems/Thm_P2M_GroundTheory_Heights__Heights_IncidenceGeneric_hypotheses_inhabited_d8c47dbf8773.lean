-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hypotheses_inhabited_d8c47dbf8773
-- name    : P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hypotheses_inhabited_d8c47dbf8773
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:21:06.513837+00:00
-- url     : https://prove2.me/theorems/b8a7b12e-9cfa-5b8c-b630-78296dd70108
-- title:
--   P2 M Ground Theory Heights  Heights Incidence Generic hypotheses inhabited d8c47dbf8773: P2 M Ground Theory Heights  Heights Incidence Generic hypotheses inhabited d8c47dbf8773
-- statement:
--   The P2 M Ground Theory Heights  Heights Incidence Generic hypotheses inhabited d8c47dbf8773 construction uses the P2 M Ground Theory Heights  Heights Incidence Generic hypotheses inhabited d8c47dbf8773 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Statements.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Statements.lean#L106-L112

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

theorem P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hypotheses_inhabited_d8c47dbf8773 :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).IsPrime ∧
      ∑ j, (fun _ => (genPt (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 0)⁻¹) j *
        genPt (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) j = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IncidenceGeneric».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hypotheses_inhabited_d8c47dbf8773
