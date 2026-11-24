-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_le_comap_killBlocks_2335735e93b1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_le_comap_killBlocks_2335735e93b1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:39.969696+00:00
-- url     : https://prove2.me/theorems/e88dbc6c-0a5e-4a4f-a8ce-1a0d2c175e33
-- title:
--   P2 M Ground Theory Heights  Heights Inter le comap kill Blocks 2335735e93b1: P2 M Ground Theory Heights  Heights Inter le comap kill Blocks 2335735e93b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter le comap kill Blocks 2335735e93b1 construction uses the P2 M Ground Theory Heights  Heights Inter le comap kill Blocks 2335735e93b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArithVarZero.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArithVarZero.lean#L68-L76

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

theorem P2M_GroundTheory_Heights__Heights_Inter_le_comap_killBlocks_2335735e93b1 {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (S : Set K) :
    P ≤ P.comap (killBlocks S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«le_comap_killBlocks» := P2M_GroundTheory_Heights__Heights_Inter_le_comap_killBlocks_2335735e93b1
