-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_kerC_79b4646adddb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_kerC_79b4646adddb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:26:07.541638+00:00
-- url     : https://prove2.me/theorems/2af9b826-06ec-5f33-bf6f-11f597267ec4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ker C 79b4646adddb: P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ker C 79b4646adddb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ker C 79b4646adddb construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ker C 79b4646adddb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L259-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L259-L289

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_kerC_79b4646adddb : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ y, Rel n X 0 y → y ∈ bdry X.dC n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«Stair».«DblData».«kerC» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_kerC_79b4646adddb
