-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_exA_437e52c8f7d5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_exA_437e52c8f7d5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:26:05.516265+00:00
-- url     : https://prove2.me/theorems/f0f4dc1d-0910-4d6b-a110-a6e03823ccc6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ex A 437e52c8f7d5: P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ex A 437e52c8f7d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ex A 437e52c8f7d5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ex A 437e52c8f7d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L196-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L196-L215

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_exA_437e52c8f7d5 : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x, X.dA n x = 0 → ∃ y, Rel n X x y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«Stair».«DblData».«exA» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_exA_437e52c8f7d5
