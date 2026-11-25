-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_powBlock_lift_not_mem_9ee24b4d2854
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_powBlock_lift_not_mem_9ee24b4d2854
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:39.38096+00:00
-- url     : https://prove2.me/theorems/e20d899c-8de6-4882-a34a-fc069e1e9ace
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close pow Block lift not mem 9ee24b4d2854: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close pow Block lift no
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close pow Block lift not mem 9ee24b4d2854 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close pow Block lift not mem 9ee24b4d2854 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L256-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L256-L268

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
open AddBlockData
variable (n)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_powBlock_lift_not_mem_9ee24b4d2854 (k₀ : ι) (e : ℕ) (c : (k : ι) → Fin (n k + 1))
    (j : Fin (n k₀ + 1)) :
    (powBlock n k₀ e).lift ((powChartForms n k₀ e).g c j) ∉ (powBlock n k₀ e).ext := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«powBlock_lift_not_mem» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_powBlock_lift_not_mem_9ee24b4d2854
