-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weightedDegree_hypotheses_point_dd0296dc5deb
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weightedDegree_hypotheses_point_dd0296dc5deb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:16:45.43084+00:00
-- url     : https://prove2.me/theorems/c33fbf94-8047-46a9-a6ac-b70cafe4e969
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weighted Degree hypotheses point dd0296dc5deb: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weighte
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weighted Degree hypotheses point dd0296dc5deb construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weighted Degree hypotheses point dd0296dc5deb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L678-L690
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L678-L690

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weightedDegree_hypotheses_point_dd0296dc5deb :
    ringKrullDim (MvPolynomial (Coord projectivePointSizes) ℤ ⧸ (ArithVariety.whole projectivePointSizes).ideal) =
      ((0 + 1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧ Nat.Prime 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«weightedDegree_hypotheses_point» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weightedDegree_hypotheses_point_dd0296dc5deb
