-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_placesRing_4624459aa66d
-- name    : P2M_GroundTheory_Heights__Heights_mem_placesRing_4624459aa66d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:04.026132+00:00
-- url     : https://prove2.me/theorems/76067b02-5f7b-429f-9f65-3d34d70a93cb
-- title:
--   P2 M Ground Theory Heights  Heights mem places Ring 4624459aa66d: P2 M Ground Theory Heights  Heights mem places Ring 4624459aa66d
-- statement:
--   The P2 M Ground Theory Heights  Heights mem places Ring 4624459aa66d construction uses the P2 M Ground Theory Heights  Heights mem places Ring 4624459aa66d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightPlacesRing.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightPlacesRing.lean#L18-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlacesRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField

theorem P2M_GroundTheory_Heights__Heights_mem_placesRing_4624459aa66d {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) (x : L) :
    x ∈ placesRing S ↔ ∀ w ∈ S, w x ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_placesRing» := P2M_GroundTheory_Heights__Heights_mem_placesRing_4624459aa66d
