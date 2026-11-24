-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_hh_18a00f98fcef
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_hh_18a00f98fcef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:52.40036+00:00
-- url     : https://prove2.me/theorems/55105929-ad6d-4981-b342-2bc3d6bbd780
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good hh 18a00f98fcef: P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good hh 18a00f98fcef
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good hh 18a00f98fcef construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair Dbl Data Good hh 18a00f98fcef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L125-L128

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_hh_18a00f98fcef {X : DblData R} (hX : X.Good) (p q : ℕ) (z : X.D p q) : X.h p (q + 1) (X.h p q z) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«Stair».«DblData».«Good».«hh» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_hh_18a00f98fcef
