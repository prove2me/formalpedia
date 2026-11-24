-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_mem_chartRing_8f356cccfc37
-- name    : P2M_GroundTheory_Heights__Heights_Model_intCast_mem_chartRing_8f356cccfc37
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:41.448885+00:00
-- url     : https://prove2.me/theorems/101a11d3-923c-4691-97fd-de5522a12609
-- title:
--   P2 M Ground Theory Heights  Heights Model int Cast mem chart Ring 8f356cccfc37: P2 M Ground Theory Heights  Heights Model int Cast mem chart Ring 8f356cccfc37
-- statement:
--   The P2 M Ground Theory Heights  Heights Model int Cast mem chart Ring 8f356cccfc37 construction uses the P2 M Ground Theory Heights  Heights Model int Cast mem chart Ring 8f356cccfc37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L13-L15

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

theorem P2M_GroundTheory_Heights__Heights_Model_intCast_mem_chartRing_8f356cccfc37 (R : Type*) [CommRing R] [Algebra R Ω] (z : ℤ) :
    (z : Ω) ∈ chartRing R x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«intCast_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Model_intCast_mem_chartRing_8f356cccfc37
