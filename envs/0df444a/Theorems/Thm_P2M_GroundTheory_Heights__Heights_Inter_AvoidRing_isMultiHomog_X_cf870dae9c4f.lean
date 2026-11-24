-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_X_cf870dae9c4f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_X_cf870dae9c4f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:46.984386+00:00
-- url     : https://prove2.me/theorems/1e7f4bb4-fb44-438b-b5ed-8f06ae6e0a38
-- title:
--   P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog X cf870dae9c4f: P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog X cf870dae9c4f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog X cf870dae9c4f construction uses the P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog X cf870dae9c4f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L31-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter GroundTheory.Heights₂.Heights.Inter.AvoidRing
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_X_cf870dae9c4f [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver R ι) (Pi.single k 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«AvoidRing».«isMultiHomog_X» := P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_X_cf870dae9c4f
