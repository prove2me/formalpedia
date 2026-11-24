-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_c_b833fd7a394e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_c_b833fd7a394e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:48.855847+00:00
-- url     : https://prove2.me/theorems/b61c021c-048b-476b-b4c2-79f776f5b14f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good ex c b833fd7a394e: P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good ex c b833fd7a394e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good ex c b833fd7a394e construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good ex c b833fd7a394e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L119-L123

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_c_b833fd7a394e {X : DblData R} (hX : X.Good) (q : ℕ) {z : X.D 0 q} (hz : X.v 0 q z = 0) :
    ∃ y, X.c q y = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«Stair».«DblData».«Good».«ex_c» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_c_b833fd7a394e
