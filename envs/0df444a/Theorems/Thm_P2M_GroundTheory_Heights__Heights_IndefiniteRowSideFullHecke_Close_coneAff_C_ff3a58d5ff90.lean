-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_C_ff3a58d5ff90
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_C_ff3a58d5ff90
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:24.887189+00:00
-- url     : https://prove2.me/theorems/43acb5ca-4214-4067-a4d7-8757e23180a7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff C ff3a58d5ff90: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff C ff3a58d5ff90
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff C ff3a58d5ff90 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff C ff3a58d5ff90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L72-L77

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_C_ff3a58d5ff90 (c : K) : coneAff K r (C c) = C (algebraMap K _ c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«coneAff_C» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_C_ff3a58d5ff90
