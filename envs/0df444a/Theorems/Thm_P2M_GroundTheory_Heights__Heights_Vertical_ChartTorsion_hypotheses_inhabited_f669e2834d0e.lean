-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_hypotheses_inhabited_f669e2834d0e
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_hypotheses_inhabited_f669e2834d0e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:40:52.110226+00:00
-- url     : https://prove2.me/theorems/13c4b4d3-017d-5b6c-b0fe-4598e798f195
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Torsion hypotheses inhabited f669e2834d0e: P2 M Ground Theory Heights  Heights Vertical Chart Torsion hypotheses inhabited f669e2834d0e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Torsion hypotheses inhabited f669e2834d0e construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Torsion hypotheses inhabited f669e2834d0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/Inhabitants.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/Inhabitants.lean#L28-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_hypotheses_inhabited_f669e2834d0e :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℤ)).IsPrime ∧
      (∀ c : ℤ, C c ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℤ)) → c = 0) ∧
      C (1 : ℤ) * (0 : MvPolynomial (Fin 1 ⊕ (Fin 1 × Fin 1)) ℤ) ∈ incIdeal ⊥ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartTorsion».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_hypotheses_inhabited_f669e2834d0e
