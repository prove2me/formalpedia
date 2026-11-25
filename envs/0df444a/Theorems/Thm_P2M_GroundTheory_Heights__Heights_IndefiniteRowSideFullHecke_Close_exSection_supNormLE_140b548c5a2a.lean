-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exSection_supNormLE_140b548c5a2a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exSection_supNormLE_140b548c5a2a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:24:14.364748+00:00
-- url     : https://prove2.me/theorems/4792080c-2fa5-5a9d-930e-a2a6bf6ad7d8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close ex Section sup Norm LE 140b548c5a2a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close ex Section sup No
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close ex Section sup Norm LE 140b548c5a2a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close ex Section sup Norm LE 140b548c5a2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L628-L641
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L628-L641

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exSection_supNormLE_140b548c5a2a :
    IntegralSection.SupNormLE (powDivStd (HermLine.standard projectiveLineSizes) 1) exSection 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«exSection_supNormLE» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exSection_supNormLE_140b548c5a2a
