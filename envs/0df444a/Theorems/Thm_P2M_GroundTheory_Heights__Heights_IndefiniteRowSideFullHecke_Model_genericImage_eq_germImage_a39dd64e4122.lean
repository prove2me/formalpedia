-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericImage_eq_germImage_a39dd64e4122
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericImage_eq_germImage_a39dd64e4122
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:00.755598+00:00
-- url     : https://prove2.me/theorems/87b66a63-aaa1-4794-ab70-9feedcd3d735
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Image eq germ Image a39dd64e4122: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Imag
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Image eq germ Image a39dd64e4122 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model generic Image eq germ Image a39dd64e4122 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GenericImageEqGermImage.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GenericImageEqGermImage.lean#L24-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GenericImageEqGermImage
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
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
variable {X : Scheme.{u}}
variable [IrreducibleSpace X]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericImage_eq_germImage_a39dd64e4122 (E : X.Modules) (x : X) :
    (GroundTheory.Heights₂.Heights.Model.genericImage E x : Set (E.presheaf.stalk (genericPoint X))) =
      germImage E x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«genericImage_eq_germImage» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericImage_eq_germImage_a39dd64e4122
