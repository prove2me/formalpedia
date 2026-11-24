-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_loc_47fca36ef53c
-- name    : P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_loc_47fca36ef53c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:43.635855+00:00
-- url     : https://prove2.me/theorems/042220d7-3160-4033-8d7a-784781b997f3
-- title:
--   P2 M Ground Theory Heights  Heights Model inv mem chart Ring loc 47fca36ef53c: P2 M Ground Theory Heights  Heights Model inv mem chart Ring loc 47fca36ef53c
-- statement:
--   The P2 M Ground Theory Heights  Heights Model inv mem chart Ring loc 47fca36ef53c construction uses the P2 M Ground Theory Heights  Heights Model inv mem chart Ring loc 47fca36ef53c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L31-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L31-L42

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

theorem P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_loc_47fca36ef53c {t : ℤ} (ht : t ∈ T) :
    (t : Ω) ≠ 0 ∧ (t : Ω)⁻¹ ∈ chartRing R x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«inv_mem_chartRing_loc» := P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_loc_47fca36ef53c
