-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_invOpen_mul_2a5fb138143a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_invOpen_mul_2a5fb138143a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:32.615076+00:00
-- url     : https://prove2.me/theorems/c5d1b245-725c-413f-9705-49ec49f30ea5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model inv Open mul 2a5fb138143a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model inv Open mul 2a5fb138143a
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model inv Open mul 2a5fb138143a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model inv Open mul 2a5fb138143a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L68-L71

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
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
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_invOpen_mul_2a5fb138143a (X : Scheme.{0}) (a b : ℕ) :
    invOpen X (a * b) = invOpen X a ⊓ invOpen X b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«invOpen_mul» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_invOpen_mul_2a5fb138143a
