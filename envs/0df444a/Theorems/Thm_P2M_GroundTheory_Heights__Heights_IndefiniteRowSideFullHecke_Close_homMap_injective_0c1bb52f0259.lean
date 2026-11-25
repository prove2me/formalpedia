-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homMap_injective_0c1bb52f0259
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homMap_injective_0c1bb52f0259
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:25:33.334235+00:00
-- url     : https://prove2.me/theorems/490bdbcd-539a-5d64-8ea0-50f7a18740c8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Map injective 0c1bb52f0259: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Map injective 0c1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Map injective 0c1bb52f0259 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close hom Map injective 0c1bb52f0259 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L49-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
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
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
variable (K : Type) [Field K] (r : ℕ)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homMap_injective_0c1bb52f0259 : Function.Injective (homMap K r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«homMap_injective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homMap_injective_0c1bb52f0259
