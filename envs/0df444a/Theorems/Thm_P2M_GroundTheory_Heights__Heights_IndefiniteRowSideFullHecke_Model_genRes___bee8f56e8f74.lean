-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genRes___bee8f56e8f74
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genRes___bee8f56e8f74
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:20.322004+00:00
-- url     : https://prove2.me/theorems/0b8f3455-4ab9-49a6-aaac-0b040f004361
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen Res   bee8f56e8f74: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen Res   bee8f56e8f74
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen Res   bee8f56e8f74 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen Res   bee8f56e8f74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L143-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L143-L144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff
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
open CategoryTheory AlgebraicGeometry
variable (X : Scheme.{0})

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genRes___bee8f56e8f74 (a : ℕ) : genRes X a ≫ (invOpen X a).ι = (genOpen X a).ι ≫ genTo X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«genRes_ι» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genRes___bee8f56e8f74
