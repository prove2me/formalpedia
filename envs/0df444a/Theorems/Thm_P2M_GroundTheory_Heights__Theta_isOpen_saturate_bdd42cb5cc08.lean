-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_isOpen_saturate_bdd42cb5cc08
-- name    : P2M_GroundTheory_Heights__Theta_isOpen_saturate_bdd42cb5cc08
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:53:54.117857+00:00
-- url     : https://prove2.me/theorems/1a397940-721d-43a6-b154-6acee4b4321b
-- title:
--   P2 M Ground Theory Heights  Theta is Open saturate bdd42cb5cc08: P2 M Ground Theory Heights  Theta is Open saturate bdd42cb5cc08
-- statement:
--   The P2 M Ground Theory Heights  Theta is Open saturate bdd42cb5cc08 construction uses the P2 M Ground Theory Heights  Theta is Open saturate bdd42cb5cc08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L43-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FundDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]

theorem P2M_GroundTheory_Heights__Theta_isOpen_saturate_bdd42cb5cc08 (Γ : Subgroup G) {A : Set G} (hA : IsOpen A) : IsOpen (saturate Γ A) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«isOpen_saturate» := P2M_GroundTheory_Heights__Theta_isOpen_saturate_bdd42cb5cc08
