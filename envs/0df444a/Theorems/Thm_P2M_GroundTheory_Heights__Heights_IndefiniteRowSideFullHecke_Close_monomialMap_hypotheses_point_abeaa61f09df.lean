-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_monomialMap_hypotheses_point_abeaa61f09df
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_monomialMap_hypotheses_point_abeaa61f09df
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:42.517289+00:00
-- url     : https://prove2.me/theorems/23b38222-b73f-4f27-9b52-830863a62c60
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close monomial Map hypotheses point abeaa61f09df: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close monomial M
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close monomial Map hypotheses point abeaa61f09df construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close monomial Map hypotheses point abeaa61f09df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L654-L676
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L654-L676

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_monomialMap_hypotheses_point_abeaa61f09df :
    (∀ k, (HermLine.standard projectivePointSizes).deg k = ((fun _ ↦ 1 : Unit → ℕ) k : ℤ)) ∧
      MonomialsBoundedBy (ArithVariety.whole projectivePointSizes) (HermLine.standard projectivePointSizes) (fun _ ↦ 1) ∧ 0 < 1 ∧
      (∀ k, ∑ i, (fun _ ↦ 1 : Coord projectivePointSizes → ℕ) ⟨k, i⟩ = 1) ∧
      val (ArithVariety.whole projectivePointSizes) (monomialOf (fun _ ↦ 1)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«monomialMap_hypotheses_point» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_monomialMap_hypotheses_point_abeaa61f09df
