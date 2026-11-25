-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_iff_of_loc_5644dbfd8277
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_iff_of_loc_5644dbfd8277
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:09.797703+00:00
-- url     : https://prove2.me/theorems/3b83fb7f-b6d5-4bd1-a612-e509ebf4bd11
-- title:
--   P2 M Ground Theory Heights  Heights Model exists pow smul mem iff of loc 5644dbfd8277: P2 M Ground Theory Heights  Heights Model exists pow smul mem iff of loc 5644dbfd8277
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists pow smul mem iff of loc 5644dbfd8277 construction uses the P2 M Ground Theory Heights  Heights Model exists pow smul mem iff of loc 5644dbfd8277 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L20-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L20-L42

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

theorem P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_iff_of_loc_5644dbfd8277 (A : S) (X Y : AddSubgroup E) {u f : Ω} (j : ℕ)
    (hu0 : u ≠ 0) (huA : u ∈ A) (hg : u ^ j * f ∈ A) (hXA : ∀ a ∈ A, ∀ e ∈ X, a • e ∈ X)
    (hXY : X ≤ Y) (hYu : ∀ e ∈ Y, u⁻¹ • e ∈ Y) (hYX : ∀ e ∈ Y, ∃ k : ℕ, u ^ k • e ∈ X) (e : E) :
    (∃ n : ℕ, (u ^ (j + 1) * f) ^ n • e ∈ X) ↔ ∃ n : ℕ, f ^ n • e ∈ Y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_pow_smul_mem_iff_of_loc» := P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_iff_of_loc_5644dbfd8277
