-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_length_quot_map_eq_3ef1ee9624d4
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_length_quot_map_eq_3ef1ee9624d4
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:05.350233+00:00
-- url     : https://prove2.me/theorems/dad67cd1-400d-4bc8-acf1-01d8b3366f81
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult length quot map eq 3ef1ee9624d4: P2 M Ground Theory Heights  Heights Orbit Chart Mult length quot map eq 3ef1ee9624d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult length quot map eq 3ef1ee9624d4 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult length quot map eq 3ef1ee9624d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L301-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L301-L310

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {R B : Type*} [CommRing R] [CommRing B]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_length_quot_map_eq_3ef1ee9624d4 {A : Type*} [CommRing A] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) (I : Ideal A) :
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«length_quot_map_eq» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_length_quot_map_eq_3ef1ee9624d4
