-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_X_4498be14a2db
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_X_4498be14a2db
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:07.097256+00:00
-- url     : https://prove2.me/theorems/5e82990e-0e49-4954-85c3-8fe4bb73b9f2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff X 4498be14a2db: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff X 4498be14a2db
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff X 4498be14a2db construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close cone Aff X 4498be14a2db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L79-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L79-L95

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_X_4498be14a2db (j : Fin (r + 1)) : coneAff K r (X j) = C (affGen K r j) * X () := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«coneAff_X» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_X_4498be14a2db
