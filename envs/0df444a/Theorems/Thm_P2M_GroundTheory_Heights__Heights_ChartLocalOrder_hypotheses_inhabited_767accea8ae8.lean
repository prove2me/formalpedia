-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocalOrder_hypotheses_inhabited_767accea8ae8
-- name    : P2M_GroundTheory_Heights__Heights_ChartLocalOrder_hypotheses_inhabited_767accea8ae8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:28.019525+00:00
-- url     : https://prove2.me/theorems/208c87e3-cb2a-534a-a441-568921fdf147
-- title:
--   P2 M Ground Theory Heights  Heights Chart Local Order hypotheses inhabited 767accea8ae8: P2 M Ground Theory Heights  Heights Chart Local Order hypotheses inhabited 767accea8ae8
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Local Order hypotheses inhabited 767accea8ae8 construction uses the P2 M Ground Theory Heights  Heights Chart Local Order hypotheses inhabited 767accea8ae8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L312-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L312-L322

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExists_hypotheses_inhabited_14e3f44c07a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormMultiHomog_hypotheses_inhabited_5f098e91ca8b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeDimComponent_hypotheses_inhabited_6ccab7e1ea7a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeDimOfChowForm_hypotheses_inhabited_5ea052711d29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FGNullstellensatz_hypotheses_inhabited_7f04cfac262e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncIdealPrime_hypotheses_inhabited_84cd1223ff65
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hypotheses_inhabited_d8c47dbf8773
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthQuotientDet_hypotheses_inhabited_8011761324cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerMul_hypotheses_inhabited_95e2ae5d82a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimeHomog_hypotheses_inhabited_0ebf35365ba4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrdPolynomialLocalization_hypotheses_inhabited_9d39a36238cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjNullstellensatz_hypotheses_inhabited_a6fca8640d3a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionOrder_hypotheses_inhabited_cb85664a66ad
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
open LineChowForm

theorem P2M_GroundTheory_Heights__Heights_ChartLocalOrder_hypotheses_inhabited_767accea8ae8 :
    (IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ Prime qLine ∧
      (Ideal.span {qLine}).IsPrime ∧
      ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine) ∧
    (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ∈
        relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔ Ideal.span {linForm uLine}) ∧
      qLine ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ∧
      linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLocalOrder».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ChartLocalOrder_hypotheses_inhabited_767accea8ae8
