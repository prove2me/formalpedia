-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_bdryC_efabaa479b6b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_bdryC_efabaa479b6b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:50.807397+00:00
-- url     : https://prove2.me/theorems/15475d4c-506f-4d6a-853d-19cb95a5a6ab
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data bdry C efabaa479b6b: P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data bdry C efabaa479b6b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data bdry C efabaa479b6b construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data bdry C efabaa479b6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L401-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L401-L408

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_bdryC_efabaa479b6b (X : DblData R) (hX : X.Good) : ∀ (n : ℕ) (y : X.C n), y ∈ bdry X.dC n → Rel n X 0 y
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«Stair».«DblData».«bdryC» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_bdryC_efabaa479b6b
