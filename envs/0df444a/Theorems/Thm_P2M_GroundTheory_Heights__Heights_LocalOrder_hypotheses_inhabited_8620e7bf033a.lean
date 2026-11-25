-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalOrder_hypotheses_inhabited_8620e7bf033a
-- name    : P2M_GroundTheory_Heights__Heights_LocalOrder_hypotheses_inhabited_8620e7bf033a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:57:08.975897+00:00
-- url     : https://prove2.me/theorems/a514671e-37b2-5ae8-8cc1-efeb46e93cea
-- title:
--   P2 M Ground Theory Heights  Heights Local Order hypotheses inhabited 8620e7bf033a: P2 M Ground Theory Heights  Heights Local Order hypotheses inhabited 8620e7bf033a
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Order hypotheses inhabited 8620e7bf033a construction uses the P2 M Ground Theory Heights  Heights Local Order hypotheses inhabited 8620e7bf033a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L333-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L333-L371

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

theorem P2M_GroundTheory_Heights__Heights_LocalOrder_hypotheses_inhabited_8620e7bf033a :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) = (0 + 1 : ℕ) ∧
      linForm (fun _ : Fin 1 => (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)) ∈
        ((⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ⊔ Ideal.span {linForm fun _ : Fin 1 => (1 : ℂ)}).minimalPrimes ∧
      (0 : Fin 1 → ℂ) ∈ zeroSet (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      (∃ N ∈ 𝓝 (0 : Fin 1 → ℂ), zeroSet (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∩ N ⊆
        ⋃ b : Fin 1, ((fun _ => lineBranch) b).image) ∧
      (∃ N ∈ 𝓝 (0 : Fin 1 → ℂ), ∀ b : Fin 1,
        zeroSet (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)) ∩ N ⊆
          ((fun _ => lineBranch) b).slice) ∧
      (∀ b b' : Fin 1, b ≠ b' → ((fun _ => lineBranch) b).image ∩ ((fun _ => lineBranch) b').image ⊆
        {x | linEval (fun _ => 1) x = 0}) ∧
      (∀ b : Fin 1, VanishesToOrder (fun t => linEval (fun _ => 1) (((fun _ => lineBranch) b).toFun t))
        ((fun _ => lineBranch) b).radius ((fun _ => 1) b)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalOrder».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_LocalOrder_hypotheses_inhabited_8620e7bf033a
