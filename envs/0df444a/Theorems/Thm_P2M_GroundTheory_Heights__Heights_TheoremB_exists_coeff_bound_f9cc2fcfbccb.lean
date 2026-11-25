-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_exists_coeff_bound_f9cc2fcfbccb
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_exists_coeff_bound_f9cc2fcfbccb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:38.5421+00:00
-- url     : https://prove2.me/theorems/3a1a4e7a-5c75-53e4-a21c-eda9b4c5c3d3
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B exists coeff bound f9cc2fcfbccb: P2 M Ground Theory Heights  Heights Theorem B exists coeff bound f9cc2fcfbccb
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B exists coeff bound f9cc2fcfbccb construction uses the P2 M Ground Theory Heights  Heights Theorem B exists coeff bound f9cc2fcfbccb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L322-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L322-L327

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
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

theorem P2M_GroundTheory_Heights__Heights_TheoremB_exists_coeff_bound_f9cc2fcfbccb {σ : Type*} (P : MvPolynomial σ ℝ) : ∃ M : ℝ, ∀ m, |coeff m P| ≤ M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«exists_coeff_bound» := P2M_GroundTheory_Heights__Heights_TheoremB_exists_coeff_bound_f9cc2fcfbccb
