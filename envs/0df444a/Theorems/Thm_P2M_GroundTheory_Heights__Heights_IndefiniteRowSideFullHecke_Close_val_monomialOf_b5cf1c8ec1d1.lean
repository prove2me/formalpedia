-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_val_monomialOf_b5cf1c8ec1d1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_val_monomialOf_b5cf1c8ec1d1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:12.407812+00:00
-- url     : https://prove2.me/theorems/c8aa58e8-b4ac-4ef4-8027-4fcb19d06f13
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close val monomial Of b5cf1c8ec1d1: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close val monomial Of b5cf1c8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close val monomial Of b5cf1c8ec1d1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close val monomial Of b5cf1c8ec1d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L617-L619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L617-L619

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_val_monomialOf_b5cf1c8ec1d1 (P : ArithVariety n) (μ : Coord n → ℕ) :
    val P (monomialOf μ) = ∏ v, genPt P v ^ μ v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«val_monomialOf» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_val_monomialOf_b5cf1c8ec1d1
