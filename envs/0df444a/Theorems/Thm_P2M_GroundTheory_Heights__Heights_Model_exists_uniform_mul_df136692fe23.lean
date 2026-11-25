-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_uniform_mul_df136692fe23
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_uniform_mul_df136692fe23
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:58.234611+00:00
-- url     : https://prove2.me/theorems/1b7dfb6e-320b-4244-a794-77b1f0e6ab3e
-- title:
--   P2 M Ground Theory Heights  Heights Model exists uniform mul df136692fe23: P2 M Ground Theory Heights  Heights Model exists uniform mul df136692fe23
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists uniform mul df136692fe23 construction uses the P2 M Ground Theory Heights  Heights Model exists uniform mul df136692fe23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L62-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L62-L76

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

theorem P2M_GroundTheory_Heights__Heights_Model_exists_uniform_mul_df136692fe23 (T : Submonoid ℤ) (A : S) (L : AddSubgroup E)
    (hLA : ∀ a ∈ A, ∀ e ∈ L, a • e ∈ L) {ζ : Ω} (hζ : ζ ∈ A) {ι : Type*} [Fintype ι] (w : ι → E)
    (h : ∀ l, ∃ t ∈ T, ∃ n : ℕ, ((t : Ω) * ζ ^ n) • w l ∈ L) :
    ∃ t ∈ T, ∃ n : ℕ, ∀ l, ∀ n' ≥ n, ((t : Ω) * ζ ^ n') • w l ∈ L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_uniform_mul» := P2M_GroundTheory_Heights__Heights_Model_exists_uniform_mul_df136692fe23
