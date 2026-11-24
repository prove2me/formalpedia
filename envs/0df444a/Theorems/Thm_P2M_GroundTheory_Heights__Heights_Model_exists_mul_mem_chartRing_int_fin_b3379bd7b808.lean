-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_mul_mem_chartRing_int_fin_b3379bd7b808
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_mul_mem_chartRing_int_fin_b3379bd7b808
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:20.326334+00:00
-- url     : https://prove2.me/theorems/0d39aaac-9b82-4bf2-90cc-f253bb9ad7f8
-- title:
--   P2 M Ground Theory Heights  Heights Model exists mul mem chart Ring int fin b3379bd7b808: P2 M Ground Theory Heights  Heights Model exists mul mem chart Ring int fin b3379bd7b808
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists mul mem chart Ring int fin b3379bd7b808 construction uses the P2 M Ground Theory Heights  Heights Model exists mul mem chart Ring int fin b3379bd7b808 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L73-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L73-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
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
variable {Ω : Type*} [Field Ω] {τ : Type*} (x : τ → Ω) (i : τ)
variable (R : Type*) [CommRing R] [Algebra ℤ R] (T : Submonoid ℤ) [IsLocalization T R] [Algebra R Ω]

theorem P2M_GroundTheory_Heights__Heights_Model_exists_mul_mem_chartRing_int_fin_b3379bd7b808 {ι : Type*} [Fintype ι] (y : ι → Ω)
    (hy : ∀ l, y l ∈ chartRing R x i) :
    ∃ t ∈ T, ∀ l, (t : Ω) * y l ∈ chartRing ℤ x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_mul_mem_chartRing_int_fin» := P2M_GroundTheory_Heights__Heights_Model_exists_mul_mem_chartRing_int_fin_b3379bd7b808
