-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_const_4bc76094e94d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_const_4bc76094e94d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:23.831944+00:00
-- url     : https://prove2.me/theorems/a7c8d590-f1f9-49d3-bc4c-77a1dffbe877
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Partition const 4bc76094e94d: P2 M Ground Theory Heights  Heights Kleiman Cech Partition const 4bc76094e94d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Partition const 4bc76094e94d construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Partition const 4bc76094e94d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L127-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L127-L138

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_const_c2206a989483

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_const_4bc76094e94d {z : Cech.Cochain (fun _ : Cell U => V) 0}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 z = 0)
    (I K : Cech.Idx U 0) : z I = z K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Partition».«const» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_const_4bc76094e94d
