-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_pow_d8f8cabc5022
-- name    : P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_pow_d8f8cabc5022
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:33.724815+00:00
-- url     : https://prove2.me/theorems/a884e179-bb82-4ae7-9e2a-167ad536f545
-- title:
--   P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog pow d8f8cabc5022: P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog pow d8f8cabc5022
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog pow d8f8cabc5022 construction uses the P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog pow d8f8cabc5022 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L45-L51

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

theorem P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_pow_d8f8cabc5022 {f : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«AvoidRing».«isMultiHomog_pow» := P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_pow_d8f8cabc5022
