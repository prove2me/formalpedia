-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_injective_48d5d985adbe
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_injective_48d5d985adbe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:57.217142+00:00
-- url     : https://prove2.me/theorems/6cb9b4f7-e967-4fde-86be-6677b745b72f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff injective 48d5d985adbe: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff injective 48
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff injective 48d5d985adbe construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff injective 48d5d985adbe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L69-L70

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_injective_48d5d985adbe : Function.Injective (coneAff K r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«coneAff_injective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_injective_48d5d985adbe
