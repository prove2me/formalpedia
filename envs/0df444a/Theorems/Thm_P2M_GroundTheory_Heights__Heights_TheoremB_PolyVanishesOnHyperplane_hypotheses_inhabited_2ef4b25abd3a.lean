-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_PolyVanishesOnHyperplane_hypotheses_inhabited_2ef4b25abd3a
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_PolyVanishesOnHyperplane_hypotheses_inhabited_2ef4b25abd3a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:24.567066+00:00
-- url     : https://prove2.me/theorems/0558641e-2bdd-43e7-8d02-091c55eb19a0
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B Poly Vanishes On Hyperplane hypotheses inhabited 2ef4b25abd3a: P2 M Ground Theory Heights  Heights Theorem B Poly Vanishes On Hyperplane hypotheses inhabi
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B Poly Vanishes On Hyperplane hypotheses inhabited 2ef4b25abd3a construction uses the P2 M Ground Theory Heights  Heights Theorem B Poly Vanishes On Hyperplane hypotheses inhabited 2ef4b25abd3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L334-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L334-L348

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

theorem P2M_GroundTheory_Heights__Heights_TheoremB_PolyVanishesOnHyperplane_hypotheses_inhabited_2ef4b25abd3a :
    let a : Fin d1.N := ⟨0, by norm_num⟩
    let b : Fin d1.N := ⟨1, by norm_num⟩
    a ≠ b ∧
      (∃ O : Set (Weight d1), IsOpen O ∧ (O ∩ rootHyperplane d1 0 a b).Nonempty ∧
        ∀ x ∈ O ∩ rootHyperplane d1 0 a b, eval x (X (0, a) - X (0, b) : LamPoly d1) = 0) ∧
      ∀ x ∈ rootHyperplane d1 0 a b, eval x (X (0, a) - X (0, b) : LamPoly d1) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«PolyVanishesOnHyperplane».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_TheoremB_PolyVanishesOnHyperplane_hypotheses_inhabited_2ef4b25abd3a
