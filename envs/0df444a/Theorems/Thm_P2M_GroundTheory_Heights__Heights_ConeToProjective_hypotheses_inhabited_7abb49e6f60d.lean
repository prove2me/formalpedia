-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeToProjective_hypotheses_inhabited_7abb49e6f60d
-- name    : P2M_GroundTheory_Heights__Heights_ConeToProjective_hypotheses_inhabited_7abb49e6f60d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:07.611787+00:00
-- url     : https://prove2.me/theorems/abcd802e-3cf4-4adf-a401-3054eaa6330f
-- title:
--   P2 M Ground Theory Heights  Heights Cone To Projective hypotheses inhabited 7abb49e6f60d: P2 M Ground Theory Heights  Heights Cone To Projective hypotheses inhabited 7abb49e6f60d
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone To Projective hypotheses inhabited 7abb49e6f60d construction uses the P2 M Ground Theory Heights  Heights Cone To Projective hypotheses inhabited 7abb49e6f60d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L373-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L373-L380

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormBaseChange_hypotheses_inhabited_d4e9bb785044
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_BadSetSmaller_hypotheses_inhabited_518179c23e1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeScaling_hypotheses_inhabited_3ec3ee98400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_DiscriminantCover_hypotheses_inhabited_2644c95f15d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_hypotheses_inhabited_1fd1f8474422
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_GenericProjectionFinite_hypotheses_inhabited_686ed1fbed83
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ConeToProjective_hypotheses_inhabited_7abb49e6f60d :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (1 + 1) LineChowForm.D2 ∧
      linForm (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      (∀ (t : ℂ) (x : Fin 2 → ℂ), t ≠ 0 → (fun _ => (1 : ℝ)) (t • x) = (fun _ => (1 : ℝ)) x) ∧
      ContinuousOn (fun _ : Fin 2 → ℂ => (1 : ℝ)) {x | x ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeToProjective».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ConeToProjective_hypotheses_inhabited_7abb49e6f60d
