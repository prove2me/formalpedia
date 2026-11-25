-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genOpen___comp_cefde62a231a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genOpen___comp_cefde62a231a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:57:25.935923+00:00
-- url     : https://prove2.me/theorems/c7edffe7-2fbf-5c0a-890e-1fb4beffdec0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen Open   comp cefde62a231a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen Open   comp cefde62a
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen Open   comp cefde62a231a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen Open   comp cefde62a231a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L146-L148

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genOpen___comp_cefde62a231a {a : ℕ} {t : genFib X ⟶ (invOpen X a).toScheme}
    (ht : t ≫ (invOpen X a).ι = genTo X) : (genOpen X a).ι ≫ t = genRes X a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«genOpen_ι_comp» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genOpen___comp_cefde62a231a
