-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_DegVanishesOnWall_hypotheses_inhabited_856395b96dd9
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_DegVanishesOnWall_hypotheses_inhabited_856395b96dd9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:16.299659+00:00
-- url     : https://prove2.me/theorems/4cf5f06e-0df0-499f-9c6b-cd787748fb68
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B Deg Vanishes On Wall hypotheses inhabited 856395b96dd9: P2 M Ground Theory Heights  Heights Theorem B Deg Vanishes On Wall hypotheses inhabited 856395b96d
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B Deg Vanishes On Wall hypotheses inhabited 856395b96dd9 construction uses the P2 M Ground Theory Heights  Heights Theorem B Deg Vanishes On Wall hypotheses inhabited 856395b96dd9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L282-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L282-L284

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

theorem P2M_GroundTheory_Heights__Heights_TheoremB_DegVanishesOnWall_hypotheses_inhabited_856395b96dd9 :
    ∃ (u : Idx d1 → ℚ) (a b : Fin d1.N), b.val = a.val + 1 ∧ u (0, a) = u (0, b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«DegVanishesOnWall».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_TheoremB_DegVanishesOnWall_hypotheses_inhabited_856395b96dd9
