-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_linFormMap_apply_3c216662ca9b
-- name    : P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_linFormMap_apply_3c216662ca9b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:24.652173+00:00
-- url     : https://prove2.me/theorems/17d6d06a-b6d7-45b1-aa3e-2ffbf17a5244
-- title:
--   P2 M Ground Theory Heights  Heights Section Hyperplane Avoid lin Form Map apply 3c216662ca9b: P2 M Ground Theory Heights  Heights Section Hyperplane Avoid lin Form Map apply 3c216662ca9b
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Hyperplane Avoid lin Form Map apply 3c216662ca9b construction uses the P2 M Ground Theory Heights  Heights Section Hyperplane Avoid lin Form Map apply 3c216662ca9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSectionHyperplaneAvoid.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSectionHyperplaneAvoid.lean#L16-L17

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

theorem P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_linFormMap_apply_3c216662ca9b {n : ℕ} (ℓ : Fin n → ℂ) : linFormMap n ℓ = linForm ℓ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionHyperplaneAvoid».«linFormMap_apply» := P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_linFormMap_apply_3c216662ca9b
