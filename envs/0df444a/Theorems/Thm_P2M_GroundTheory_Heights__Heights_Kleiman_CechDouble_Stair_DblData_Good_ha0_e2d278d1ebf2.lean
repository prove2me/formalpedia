-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ha0_e2d278d1ebf2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ha0_e2d278d1ebf2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:45.722894+00:00
-- url     : https://prove2.me/theorems/705254b3-bfde-458d-8196-9e36174c7670
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good ha0 e2d278d1ebf2: P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good ha0 e2d278d1ebf2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good ha0 e2d278d1ebf2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good ha0 e2d278d1ebf2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L130-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L130-L133

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
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData.Good

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ha0_e2d278d1ebf2 {X : DblData R} (hX : X.Good) (p : ℕ) (x : X.A p) : X.h p 0 (X.a p x) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«Stair».«DblData».«Good».«ha0» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ha0_e2d278d1ebf2
