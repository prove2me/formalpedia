-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_d_eq_9797a3782368
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_d_eq_9797a3782368
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:38:22.888945+00:00
-- url     : https://prove2.me/theorems/37eebcc0-37ef-4ae1-9122-f178efe91427
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Partition d eq 9797a3782368: P2 M Ground Theory Heights  Heights Kleiman Cech Partition d eq 9797a3782368
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Partition d eq 9797a3782368 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Partition d eq 9797a3782368 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean#L27-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_d_eq_93862b1062b9

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_d_eq_9797a3782368 {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (K : Cech.Idx U (i + 1)) :
    Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Partition».«d_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_d_eq_9797a3782368
