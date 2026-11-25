-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_bdryA_f0cfaa09fe97
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_bdryA_f0cfaa09fe97
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:13.470926+00:00
-- url     : https://prove2.me/theorems/18969898-d35f-424b-80cc-c7eb7d4267f5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data bdry A f0cfaa09fe97: P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data bdry A f0cfaa09fe97
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data bdry A f0cfaa09fe97 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data bdry A f0cfaa09fe97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L392-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L392-L399

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.CechDouble
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type u} [CommRing R]
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_bdryA_f0cfaa09fe97 (X : DblData R) (hX : X.Good) : ∀ (n : ℕ) (x : X.A n), x ∈ bdry X.dA n → Rel n X x 0
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«Stair».«DblData».«bdryA» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_bdryA_f0cfaa09fe97
