-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_eq_baseChangeMap_b84b9ed632a9
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_eq_baseChangeMap_b84b9ed632a9
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:26:29.095786+00:00
-- url     : https://prove2.me/theorems/d32b0dd7-9e39-5076-964a-1d4c325b8d9e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen To eq base Change Map b84b9ed632a9: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen To eq base
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen To eq base Change Map b84b9ed632a9 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen To eq base Change Map b84b9ed632a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsVectorBundleIffModel.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsVectorBundleIffModel.lean#L15-L16

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_eq_baseChangeMap_b84b9ed632a9 (X : Scheme.{0}) :
    genTo X = GroundTheory.Heights₂.Heights.Model.baseChangeMap (toSpecZ X) ℚ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«genTo_eq_baseChangeMap» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_eq_baseChangeMap_b84b9ed632a9
