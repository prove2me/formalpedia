-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralSection_value_mem_chartLat_a828c5da8776
-- name    : P2M_GroundTheory_Heights__Heights_IntegralSection_value_mem_chartLat_a828c5da8776
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:05.063154+00:00
-- url     : https://prove2.me/theorems/808d6495-adaa-4499-88bf-7ba8c59aa0a5
-- title:
--   P2 M Ground Theory Heights  Heights Integral Section value mem chart Lat a828c5da8776: P2 M Ground Theory Heights  Heights Integral Section value mem chart Lat a828c5da8776
-- statement:
--   The P2 M Ground Theory Heights  Heights Integral Section value mem chart Lat a828c5da8776 construction uses the P2 M Ground Theory Heights  Heights Integral Section value mem chart Lat a828c5da8776 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L176-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L176-L203

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_IntegralSection_value_mem_chartLat_a828c5da8776 {P : ArithVariety n} {a : ι → ℤ}
    (s : IntegralSection P a) {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    (hy : ∀ f ∈ P.ideal, aeval y f = 0) (hG : aeval y s.den ≠ 0) :
    aeval y s.num / aeval y s.den ∈ Geo.chartLat (ι := blockIdx n) y a 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IntegralSection».«value_mem_chartLat» := P2M_GroundTheory_Heights__Heights_IntegralSection_value_mem_chartLat_a828c5da8776
