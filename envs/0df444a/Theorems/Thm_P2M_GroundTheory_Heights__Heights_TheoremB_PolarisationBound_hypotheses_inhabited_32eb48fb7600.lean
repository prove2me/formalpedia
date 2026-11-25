-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationBound_hypotheses_inhabited_32eb48fb7600
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationBound_hypotheses_inhabited_32eb48fb7600
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:14.76065+00:00
-- url     : https://prove2.me/theorems/4abc76aa-73d9-47de-bac2-ecf65d31c9c5
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B Polarisation Bound hypotheses inhabited 32eb48fb7600: P2 M Ground Theory Heights  Heights Theorem B Polarisation Bound hypotheses inhabited 32eb48fb7600
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B Polarisation Bound hypotheses inhabited 32eb48fb7600 construction uses the P2 M Ground Theory Heights  Heights Theorem B Polarisation Bound hypotheses inhabited 32eb48fb7600 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L329-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L329-L332

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CharacterBound_hypotheses_inhabited_d27e13b1c390
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_LemmaA_hypotheses_inhabited_db910e8699fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_PlueckerHadamard_hypotheses_inhabited_af9d0b9b23c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchurPowerSumCoefficient_hypotheses_inhabited_32aa544f21a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Section2_hypotheses_inhabited_2342196bac3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Section3_hypotheses_inhabited_6b2680fde2e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankBound_hypotheses_inhabited_4ec382f0f031

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)

theorem P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationBound_hypotheses_inhabited_32eb48fb7600 (Φ : MvPolynomial (Fin 1) ℝ →ₗ[ℝ] ℝ) :
    ((Finsupp.single (0 : Fin 1) 1).sum fun _ e => e) = 1 ∧
      ∃ M : ℝ, ∀ m', |coeff m' (polarPoly Φ 1)| ≤ M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«PolarisationBound».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationBound_hypotheses_inhabited_32eb48fb7600
