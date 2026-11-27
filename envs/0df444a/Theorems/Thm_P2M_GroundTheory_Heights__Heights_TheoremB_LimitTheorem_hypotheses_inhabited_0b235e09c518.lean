-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_LimitTheorem_hypotheses_inhabited_0b235e09c518
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_LimitTheorem_hypotheses_inhabited_0b235e09c518
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:13.626344+00:00
-- url     : https://prove2.me/theorems/f0085dec-e592-53d4-83ed-76ebaddca013
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B Limit Theorem hypotheses inhabited 0b235e09c518: P2 M Ground Theory Heights  Heights Theorem B Limit Theorem hypotheses inhabited 0b235e09c518
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B Limit Theorem hypotheses inhabited 0b235e09c518 construction uses the P2 M Ground Theory Heights  Heights Theorem B Limit Theorem hypotheses inhabited 0b235e09c518 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/StatementsEnd.lean#L391-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/StatementsEnd.lean#L391-L396

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CharacterBound_hypotheses_inhabited_d27e13b1c390
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_LemmaA_hypotheses_inhabited_db910e8699fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_PlueckerHadamard_hypotheses_inhabited_af9d0b9b23c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchurPowerSumCoefficient_hypotheses_inhabited_32aa544f21a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Section2_hypotheses_inhabited_2342196bac3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Section3_hypotheses_inhabited_6b2680fde2e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankBound_hypotheses_inhabited_4ec382f0f031
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_CompactRootVanishes_hypotheses_inhabited_8e5c3fc6f006
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_DecompositionBound_hypotheses_inhabited_3782fe01632f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_DegVanishesOnWall_hypotheses_inhabited_856395b96dd9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_DelDividesV_hypotheses_inhabited_201bd3d0b979
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_KRationalDense_hypotheses_inhabited_f2ec2e0ac3ed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationBound_hypotheses_inhabited_32eb48fb7600
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_PolyVanishesOnHyperplane_hypotheses_inhabited_2ef4b25abd3a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_ShFormula_hypotheses_inhabited_d676043f067b

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
open MvPolynomial Finset Filter Topology
variable (d : IndexData)
variable {d}

theorem P2M_GroundTheory_Heights__Heights_TheoremB_LimitTheorem_hypotheses_inhabited_0b235e09c518 :
    (0 : ℝ) < 1 ∧ ∀ s : ℚ, 0 < s → (s : ℝ) ≤ 1 →
      |(s : ℝ) - eval (fun o : Option (Fin 1) => o.elim (s : ℝ) (fun p => (0 : Fin 1 → ℝ) p - s * (0 : Fin 1 → ℝ) p))
        (X none : MvPolynomial (Option (Fin 1)) ℝ)| ≤ 0 * s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«LimitTheorem».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_TheoremB_LimitTheorem_hypotheses_inhabited_0b235e09c518
