-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_exact_of_partition_751a789b2856
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_exact_of_partition_751a789b2856
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:06:40.353902+00:00
-- url     : https://prove2.me/theorems/93b6001f-56f1-473a-8e31-f33e4af1989b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Partition exact of partition 751a789b2856: P2 M Ground Theory Heights  Heights Kleiman Cech Partition exact of partition 751a789b2856
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Partition exact of partition 751a789b2856 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Partition exact of partition 751a789b2856 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L74-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L74-L104

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_exact_of_partition_751a789b2856 {A : Type w} [Semiring A] [Module A V] (M : Cell U → Submodule R V)
    {i : ℕ} (z : Cech.Cochain (fun _ : Cell U => V) (i + 1))
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) (i + 1) z = 0)
    (a : Fin n → A) (ha : ∑ k ∈ U, a k = 1)
    (hmem : ∀ (K : Cech.Idx U i) (k : Fin n), k ∈ U → k ∉ K.1.1 →
      a k • onSet z (insert k K.1.1) ∈ M K.1) :
    ∃ t ∈ Cech.Cdeg (fun _ : Cell U => V) M i,
      Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i t = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Partition».«exact_of_partition» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_exact_of_partition_751a789b2856
