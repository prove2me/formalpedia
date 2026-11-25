-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_points_eq_conePoints_7ea46e7980ef
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_points_eq_conePoints_7ea46e7980ef
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:16.270726+00:00
-- url     : https://prove2.me/theorems/c2201cfc-eb52-5254-83ef-5d115f1337a5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close points eq cone Points 7ea46e7980ef: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close points eq cone Poi
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close points eq cone Points 7ea46e7980ef construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close points eq cone Points 7ea46e7980ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L55-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal chartLat chartLatNm secM mcPts IsArithVar)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_points_eq_conePoints_7ea46e7980ef (P : ArithVariety n) (F : Type*) [CommRing F] :
    P.points F = conePoints P.ideal F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«points_eq_conePoints» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_points_eq_conePoints_7ea46e7980ef
