-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_pair_9415c9c7ff83
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_pair_9415c9c7ff83
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:19.956795+00:00
-- url     : https://prove2.me/theorems/ce165f00-e34f-53d3-b9b0-c67e2dd2bd41
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Partition on Set pair 9415c9c7ff83: P2 M Ground Theory Heights  Heights Kleiman Cech Partition on Set pair 9415c9c7ff83
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Partition on Set pair 9415c9c7ff83 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Partition on Set pair 9415c9c7ff83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L106-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L106-L125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_pair_39898383e827

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_pair_9415c9c7ff83 {z : Cech.Cochain (fun _ : Cell U => V) 0}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 z = 0)
    {a b : Fin n} (haU : a ∈ U) (hbU : b ∈ U) (hab : a < b) : onSet z {a} = onSet z {b} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Partition».«onSet_pair» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_pair_9415c9c7ff83
