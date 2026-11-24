-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_chartRing_of_int_e441a7136a3a
-- name    : P2M_GroundTheory_Heights__Heights_Model_mem_chartRing_of_int_e441a7136a3a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:26.392823+00:00
-- url     : https://prove2.me/theorems/447ffbfb-531c-471e-bbd4-062a0bbe6de5
-- title:
--   P2 M Ground Theory Heights  Heights Model mem chart Ring of int e441a7136a3a: P2 M Ground Theory Heights  Heights Model mem chart Ring of int e441a7136a3a
-- statement:
--   The P2 M Ground Theory Heights  Heights Model mem chart Ring of int e441a7136a3a construction uses the P2 M Ground Theory Heights  Heights Model mem chart Ring of int e441a7136a3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L17-L23

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

theorem P2M_GroundTheory_Heights__Heights_Model_mem_chartRing_of_int_e441a7136a3a (R : Type*) [CommRing R] [Algebra R Ω] {y : Ω}
    (hy : y ∈ chartRing ℤ x i) : y ∈ chartRing R x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mem_chartRing_of_int» := P2M_GroundTheory_Heights__Heights_Model_mem_chartRing_of_int_e441a7136a3a
