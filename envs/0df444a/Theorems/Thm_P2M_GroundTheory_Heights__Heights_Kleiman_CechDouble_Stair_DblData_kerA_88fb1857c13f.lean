-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_kerA_88fb1857c13f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_kerA_88fb1857c13f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:26:00.577516+00:00
-- url     : https://prove2.me/theorems/d23ae971-3096-5ade-8604-d775d8de64aa
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ker A 88fb1857c13f: P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ker A 88fb1857c13f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ker A 88fb1857c13f construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data ker A 88fb1857c13f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L291-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L291-L324

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_kerA_88fb1857c13f : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x, Rel n X x 0 → x ∈ bdry X.dA n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«Stair».«DblData».«kerA» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_kerA_88fb1857c13f
