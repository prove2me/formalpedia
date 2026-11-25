-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_idx_f72ebc720009
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_idx_f72ebc720009
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:38:22.910976+00:00
-- url     : https://prove2.me/theorems/35d13cef-cbc9-503b-964f-e0f40aec2c98
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Partition on Set idx f72ebc720009: P2 M Ground Theory Heights  Heights Kleiman Cech Partition on Set idx f72ebc720009
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Partition on Set idx f72ebc720009 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Partition on Set idx f72ebc720009 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.Cech GroundTheory.Heights₂.Heights.Kleiman.Cech.Partition
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V]
  [Module R V]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_idx_f72ebc720009 {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (I : Cech.Idx U i) :
    onSet s I.1.1 = s I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Partition».«onSet_idx» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_idx_f72ebc720009
