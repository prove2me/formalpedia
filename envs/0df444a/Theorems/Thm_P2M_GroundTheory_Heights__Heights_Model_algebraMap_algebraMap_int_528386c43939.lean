-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_algebraMap_algebraMap_int_528386c43939
-- name    : P2M_GroundTheory_Heights__Heights_Model_algebraMap_algebraMap_int_528386c43939
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:48.188453+00:00
-- url     : https://prove2.me/theorems/29084bc4-58d0-4788-9783-d8117825da28
-- title:
--   P2 M Ground Theory Heights  Heights Model algebra Map algebra Map int 528386c43939: P2 M Ground Theory Heights  Heights Model algebra Map algebra Map int 528386c43939
-- statement:
--   The P2 M Ground Theory Heights  Heights Model algebra Map algebra Map int 528386c43939 construction uses the P2 M Ground Theory Heights  Heights Model algebra Map algebra Map int 528386c43939 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLoc.lean#L28-L29

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
omit [IsLocalization T R]

theorem P2M_GroundTheory_Heights__Heights_Model_algebraMap_algebraMap_int_528386c43939 (z : ℤ) : algebraMap R Ω (algebraMap ℤ R z) = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«algebraMap_algebraMap_int» := P2M_GroundTheory_Heights__Heights_Model_algebraMap_algebraMap_int_528386c43939
