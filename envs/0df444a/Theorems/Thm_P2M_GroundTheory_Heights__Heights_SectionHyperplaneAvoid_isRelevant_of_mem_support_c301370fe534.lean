-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_isRelevant_of_mem_support_c301370fe534
-- name    : P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_isRelevant_of_mem_support_c301370fe534
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:15.942364+00:00
-- url     : https://prove2.me/theorems/7772e768-79ff-4471-8649-81930fcebad8
-- title:
--   P2 M Ground Theory Heights  Heights Section Hyperplane Avoid is Relevant of mem support c301370fe534: P2 M Ground Theory Heights  Heights Section Hyperplane Avoid is Relevant of mem support c301370fe5
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Hyperplane Avoid is Relevant of mem support c301370fe534 construction uses the P2 M Ground Theory Heights  Heights Section Hyperplane Avoid is Relevant of mem support c301370fe534 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSectionHyperplaneAvoid.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSectionHyperplaneAvoid.lean#L38-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionHyperplaneAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSectionHyperplaneAvoid
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
open GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid

theorem P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_isRelevant_of_mem_support_c301370fe534 {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : W ∈ (divCycle J u).support) : IsRelevant W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionHyperplaneAvoid».«isRelevant_of_mem_support» := P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_isRelevant_of_mem_support_c301370fe534
