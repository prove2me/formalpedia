-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_ShFormula_hypotheses_inhabited_d676043f067b
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_ShFormula_hypotheses_inhabited_d676043f067b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:17.40835+00:00
-- url     : https://prove2.me/theorems/8a4215de-7aa4-4a3f-8683-ec55939103ae
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B Sh Formula hypotheses inhabited d676043f067b: P2 M Ground Theory Heights  Heights Theorem B Sh Formula hypotheses inhabited d676043f067b
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B Sh Formula hypotheses inhabited d676043f067b construction uses the P2 M Ground Theory Heights  Heights Theorem B Sh Formula hypotheses inhabited d676043f067b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L295-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L295-L320

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

theorem P2M_GroundTheory_Heights__Heights_TheoremB_ShFormula_hypotheses_inhabited_d676043f067b :
    sampleF ≠ 0 ∧ sampleF.IsHomogeneous (d1.D + 1) ∧
      (∀ k ∈ Icc 1 d1.N, ∀ τ' : Fin d1.f, (sampleQ k τ').IsHomogeneous (d1.D + 1 - k)) ∧
      RestTerms.IsPowerSumDecomposition d1.f d1.N sampleF sampleQ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«ShFormula».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_TheoremB_ShFormula_hypotheses_inhabited_d676043f067b
