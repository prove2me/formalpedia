-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isVectorBundle_iff_model_7c6200fe56e7
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isVectorBundle_iff_model_7c6200fe56e7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:25:21.860968+00:00
-- url     : https://prove2.me/theorems/3437fe88-6174-4371-9c32-53830ccd8001
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Vector Bundle iff model 7c6200fe56e7: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Vector Bun
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Vector Bundle iff model 7c6200fe56e7 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Vector Bundle iff model 7c6200fe56e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsVectorBundleIffModel.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsVectorBundleIffModel.lean#L12-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsVectorBundleIffModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isVectorBundle_iff_model_7c6200fe56e7 {X : Scheme.{0}} (E : X.Modules) :
    GroundTheory.Heights₂.Heights.Model.IsVectorBundle E ↔ IsVectorBundle E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«isVectorBundle_iff_model» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isVectorBundle_iff_model_7c6200fe56e7
