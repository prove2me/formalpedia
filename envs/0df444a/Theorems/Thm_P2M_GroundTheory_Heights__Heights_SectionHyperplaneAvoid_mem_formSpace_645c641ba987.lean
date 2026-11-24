-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_mem_formSpace_645c641ba987
-- name    : P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_mem_formSpace_645c641ba987
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:05.256751+00:00
-- url     : https://prove2.me/theorems/89c50dc5-7520-4e94-a6fa-15d054bdb9a1
-- title:
--   P2 M Ground Theory Heights  Heights Section Hyperplane Avoid mem form Space 645c641ba987: P2 M Ground Theory Heights  Heights Section Hyperplane Avoid mem form Space 645c641ba987
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Hyperplane Avoid mem form Space 645c641ba987 construction uses the P2 M Ground Theory Heights  Heights Section Hyperplane Avoid mem form Space 645c641ba987 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSectionHyperplaneAvoid.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSectionHyperplaneAvoid.lean#L22-L24

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

theorem P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_mem_formSpace_645c641ba987 {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ} :
    ℓ ∈ formSpace I ↔ linForm ℓ ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionHyperplaneAvoid».«mem_formSpace» := P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_mem_formSpace_645c641ba987
