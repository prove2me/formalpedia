-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeDimComponent_hypotheses_inhabited_6ccab7e1ea7a
-- name    : P2M_GroundTheory_Heights__Heights_ConeDimComponent_hypotheses_inhabited_6ccab7e1ea7a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:21:51.610642+00:00
-- url     : https://prove2.me/theorems/e0f03759-8962-41e9-83f7-fe1d795c3466
-- title:
--   P2 M Ground Theory Heights  Heights Cone Dim Component hypotheses inhabited 6ccab7e1ea7a: P2 M Ground Theory Heights  Heights Cone Dim Component hypotheses inhabited 6ccab7e1ea7a
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Dim Component hypotheses inhabited 6ccab7e1ea7a construction uses the P2 M Ground Theory Heights  Heights Cone Dim Component hypotheses inhabited 6ccab7e1ea7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Statements.lean#L156-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Statements.lean#L156-L167

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

theorem P2M_GroundTheory_Heights__Heights_ConeDimComponent_hypotheses_inhabited_6ccab7e1ea7a :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      ringKrullDim (MvPolynomial (Fin 2) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))) =
        ((1 + 1 : ℕ) : WithBot ℕ∞) ∧
      linForm (fun j : Fin 2 => if j = 0 then (1 : ℚ) else 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      Ideal.span {X 0} ∈ relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔
        Ideal.span {linForm (fun j : Fin 2 => if j = 0 then (1 : ℚ) else 0)}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeDimComponent».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ConeDimComponent_hypotheses_inhabited_6ccab7e1ea7a
