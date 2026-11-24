-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_killBlocks_comp_73c8076a9a36
-- name    : P2M_GroundTheory_Heights__Heights_Inter_killBlocks_comp_73c8076a9a36
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:24.201857+00:00
-- url     : https://prove2.me/theorems/bb02c622-4320-42c4-b1c8-4c8ef6824b07
-- title:
--   P2 M Ground Theory Heights  Heights Inter kill Blocks comp 73c8076a9a36: P2 M Ground Theory Heights  Heights Inter kill Blocks comp 73c8076a9a36
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter kill Blocks comp 73c8076a9a36 construction uses the P2 M Ground Theory Heights  Heights Inter kill Blocks comp 73c8076a9a36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArithVarZero.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArithVarZero.lean#L80-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_killBlocks_comp_73c8076a9a36 {S S' : Set K} (h : S ⊆ S') :
    (killBlocks S').comp (killBlocks S) = (killBlocks S' : MRing ι →ₐ[ℤ] MRing ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«killBlocks_comp» := P2M_GroundTheory_Heights__Heights_Inter_killBlocks_comp_73c8076a9a36
