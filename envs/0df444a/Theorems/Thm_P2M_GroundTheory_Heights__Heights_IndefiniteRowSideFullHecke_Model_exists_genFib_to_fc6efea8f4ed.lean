-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_genFib_to_fc6efea8f4ed
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_genFib_to_fc6efea8f4ed
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:52.267637+00:00
-- url     : https://prove2.me/theorems/491b5ccd-54cc-4f80-91d7-8800691c6e3b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model exists gen Fib to fc6efea8f4ed: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model exists gen Fib to fc6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model exists gen Fib to fc6efea8f4ed construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model exists gen Fib to fc6efea8f4ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L131-L136

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_genFib_to_fc6efea8f4ed {m : ℕ} (hm : m ≠ 0) :
    ∃ t : genFib X ⟶ (invOpen X m).toScheme, t ≫ (invOpen X m).ι = genTo X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«exists_genFib_to» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_genFib_to_fc6efea8f4ed
