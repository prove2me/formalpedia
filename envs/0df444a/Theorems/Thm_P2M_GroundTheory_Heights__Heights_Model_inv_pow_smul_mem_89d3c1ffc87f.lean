-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_pow_smul_mem_89d3c1ffc87f
-- name    : P2M_GroundTheory_Heights__Heights_Model_inv_pow_smul_mem_89d3c1ffc87f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:01.764253+00:00
-- url     : https://prove2.me/theorems/f0dd8233-1a82-5f6e-be51-e3ac25bf0d04
-- title:
--   P2 M Ground Theory Heights  Heights Model inv pow smul mem 89d3c1ffc87f: P2 M Ground Theory Heights  Heights Model inv pow smul mem 89d3c1ffc87f
-- statement:
--   The P2 M Ground Theory Heights  Heights Model inv pow smul mem 89d3c1ffc87f construction uses the P2 M Ground Theory Heights  Heights Model inv pow smul mem 89d3c1ffc87f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L14-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {S : Type*} [SetLike S Ω] [SubringClass S Ω]

theorem P2M_GroundTheory_Heights__Heights_Model_inv_pow_smul_mem_89d3c1ffc87f (Y : AddSubgroup E) {u : Ω} (hYu : ∀ e ∈ Y, u⁻¹ • e ∈ Y) (k : ℕ) :
    ∀ e ∈ Y, (u⁻¹) ^ k • e ∈ Y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«inv_pow_smul_mem» := P2M_GroundTheory_Heights__Heights_Model_inv_pow_smul_mem_89d3c1ffc87f
