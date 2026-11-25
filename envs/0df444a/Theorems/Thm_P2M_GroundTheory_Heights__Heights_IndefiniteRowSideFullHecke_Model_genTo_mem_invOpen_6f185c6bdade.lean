-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_mem_invOpen_6f185c6bdade
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_mem_invOpen_6f185c6bdade
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:40.007447+00:00
-- url     : https://prove2.me/theorems/1b4367a2-8226-419e-b32b-4c094d048e8d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen To mem inv Open 6f185c6bdade: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen To mem inv Open
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen To mem inv Open 6f185c6bdade construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model gen To mem inv Open 6f185c6bdade property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L124-L129

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_mem_invOpen_6f185c6bdade {m : ℕ} (hm : m ≠ 0) (x : genFib X) : (genTo X).base x ∈ invOpen X m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«genTo_mem_invOpen» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_mem_invOpen_6f185c6bdade
