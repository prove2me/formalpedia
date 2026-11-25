-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_sectionInjectivity_hypotheses_projectiveLine_55859427ce64
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_sectionInjectivity_hypotheses_projectiveLine_55859427ce64
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:56.973853+00:00
-- url     : https://prove2.me/theorems/b0a37b1e-cbc8-4965-998a-32bf39e42275
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close section Injectivity hypotheses projective Line 55859427ce64: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close section Injectivity hypotheses projective Line 55859427ce64 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close section Injectivity hypotheses projective Line 55859427ce64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L643-L652
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L643-L652

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_sectionInjectivity_hypotheses_projectiveLine_55859427ce64 :
    1 < 2 ∧ 1 ≤ 1 ∧ exSection.num ∉ (ArithVariety.whole projectiveLineSizes).ideal ∧
      IntegralSection.SupNormLE (powDivStd (HermLine.standard projectiveLineSizes) 1) exSection 0 ∧
      (powBlock projectiveLineSizes () 2).deg = (twistPow (HermLine.standard projectiveLineSizes) (2 - 1) 1 0).deg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«sectionInjectivity_hypotheses_projectiveLine» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_sectionInjectivity_hypotheses_projectiveLine_55859427ce64
