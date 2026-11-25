-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericSpecMap_closedPoint_6aa880cac864
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericSpecMap_closedPoint_6aa880cac864
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:13.0339+00:00
-- url     : https://prove2.me/theorems/a0752a34-a958-4ccb-85bc-388bc5e22abe
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Spec Map closed Point 6aa880cac864: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Sp
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Spec Map closed Point 6aa880cac864 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Spec Map closed Point 6aa880cac864 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L54-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteTypeSectionsOfIsFiniteTypeOverZ
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
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericSpecMap_closedPoint_6aa880cac864 (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] :
    _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L (IsLocalRing.closedPoint L) =
      genericPoint Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«genericSpecMap_closedPoint» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericSpecMap_closedPoint_6aa880cac864
