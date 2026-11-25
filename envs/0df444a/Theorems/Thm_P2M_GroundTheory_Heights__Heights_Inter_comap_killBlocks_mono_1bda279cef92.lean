-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_comap_killBlocks_mono_1bda279cef92
-- name    : P2M_GroundTheory_Heights__Heights_Inter_comap_killBlocks_mono_1bda279cef92
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:44.034799+00:00
-- url     : https://prove2.me/theorems/ad67331e-87ca-49e3-9ae7-e81387bbedd9
-- title:
--   P2 M Ground Theory Heights  Heights Inter comap kill Blocks mono 1bda279cef92: P2 M Ground Theory Heights  Heights Inter comap kill Blocks mono 1bda279cef92
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter comap kill Blocks mono 1bda279cef92 construction uses the P2 M Ground Theory Heights  Heights Inter comap kill Blocks mono 1bda279cef92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArithVarZero.lean#L88-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArithVarZero.lean#L88-L95

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

theorem P2M_GroundTheory_Heights__Heights_Inter_comap_killBlocks_mono_1bda279cef92 {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {S S' : Set K}
    (h : S ⊆ S') : P.comap (killBlocks S) ≤ P.comap (killBlocks S') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«comap_killBlocks_mono» := P2M_GroundTheory_Heights__Heights_Inter_comap_killBlocks_mono_1bda279cef92
