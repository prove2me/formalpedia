-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_fieldMap_injective_a32de5e1b1f5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_fieldMap_injective_a32de5e1b1f5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:23.041461+00:00
-- url     : https://prove2.me/theorems/48d9516a-acca-460c-ad61-c746c5b26cff
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close field Map injective a32de5e1b1f5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close field Map injective
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close field Map injective a32de5e1b1f5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close field Map injective a32de5e1b1f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L62-L64

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_fieldMap_injective_a32de5e1b1f5 : Function.Injective (fieldMap K r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«fieldMap_injective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_fieldMap_injective_a32de5e1b1f5
