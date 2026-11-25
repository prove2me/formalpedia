-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericSpecMap_app_iso_6054cb9c6d0f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericSpecMap_app_iso_6054cb9c6d0f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:37.36895+00:00
-- url     : https://prove2.me/theorems/3b3260b4-ca4b-436b-af8a-cbe329d8a99b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Spec Map app iso 6054cb9c6d0f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Spec Ma
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Spec Map app iso 6054cb9c6d0f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Spec Map app iso 6054cb9c6d0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L65-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteTypeSectionsOfIsFiniteTypeOverZ.lean#L65-L75

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericSpecMap_app_iso_6054cb9c6d0f (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] (U : Z.Opens) (hη : genericPoint Z ∈ U)
    (hmem : _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L (IsLocalRing.closedPoint L) ∈ U) :
    (_root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L).app U ≫
      ((Spec (CommRingCat.of L)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of L)).hom =
      Z.presheaf.germ U (genericPoint Z) hη ≫ CommRingCat.ofHom (algebraMap Z.functionField L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«genericSpecMap_app_iso» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericSpecMap_app_iso_6054cb9c6d0f
