-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_formSpace_ne_top_c7bc28259234
-- name    : P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_formSpace_ne_top_c7bc28259234
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:59.698851+00:00
-- url     : https://prove2.me/theorems/f8389263-040f-4626-8019-737cad87e2d2
-- title:
--   P2 M Ground Theory Heights  Heights Section Hyperplane Avoid form Space ne top c7bc28259234: P2 M Ground Theory Heights  Heights Section Hyperplane Avoid form Space ne top c7bc28259234
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Hyperplane Avoid form Space ne top c7bc28259234 construction uses the P2 M Ground Theory Heights  Heights Section Hyperplane Avoid form Space ne top c7bc28259234 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSectionHyperplaneAvoid.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSectionHyperplaneAvoid.lean#L26-L36

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

theorem P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_formSpace_ne_top_c7bc28259234 {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} (hI : IsRelevant I) :
    formSpace I ≠ ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionHyperplaneAvoid».«formSpace_ne_top» := P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_formSpace_ne_top_c7bc28259234
