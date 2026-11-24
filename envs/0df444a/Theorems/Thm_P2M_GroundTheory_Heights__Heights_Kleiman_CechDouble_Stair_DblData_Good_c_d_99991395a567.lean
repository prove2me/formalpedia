-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_d_99991395a567
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_d_99991395a567
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:59.363558+00:00
-- url     : https://prove2.me/theorems/f305dc25-36e9-4b49-b5c7-d7847686a98c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good c d 99991395a567: P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good c d 99991395a567
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good c d 99991395a567 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good c d 99991395a567 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L97-L99

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_d_99991395a567 {X : DblData R} (hX : X.Good) (q : ℕ) (y : X.C q) :
    X.c (q + 1) (X.dC q y) = X.h 0 q (X.c q y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«Stair».«DblData».«Good».«c_d» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_d_99991395a567
