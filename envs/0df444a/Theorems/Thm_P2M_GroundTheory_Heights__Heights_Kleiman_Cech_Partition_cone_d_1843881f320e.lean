-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_cone_d_1843881f320e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_cone_d_1843881f320e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:45.118665+00:00
-- url     : https://prove2.me/theorems/bbb353f8-4ae3-52b8-982e-a6a713578447
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Partition cone d 1843881f320e: P2 M Ground Theory Heights  Heights Kleiman Cech Partition cone d 1843881f320e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Partition cone d 1843881f320e construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Partition cone d 1843881f320e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L38-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L38-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_cone_d_1843881f320e {i : ℕ} {z : Cech.Cochain (fun _ : Cell U => V) (i + 1)}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) (i + 1) z = 0) {k : Fin n} (hk : k ∈ U)
    (K : Cech.Idx U (i + 1)) :
    ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • coneY k z (K.1.1.erase j) = z K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Partition».«cone_d» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_cone_d_1843881f320e
