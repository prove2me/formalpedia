-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_exists_partition_c437fe6b702e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_exists_partition_c437fe6b702e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:59:37.428454+00:00
-- url     : https://prove2.me/theorems/78ca7bd9-72d4-50ec-a4bb-7ad2776a4d47
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns exists partition c437fe6b702e: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns exists partition c437fe6b702e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns exists partition c437fe6b702e construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns exists partition c437fe6b702e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L135-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L135-L192

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns
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
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ}
variable {G : SubSystem S x E} {H : SubSystem S x Ω} {h : Fin (r + 1) → Ω} {I : Chart x}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_exists_partition_c437fe6b702e {H : LineBundle S x} (hV : IsVeryAmpleBy H.toSubSystem h) (I : Chart x)
    (m : ℕ) : ∃ w : Fin (r + 1) → Ω, ∑ k, w k * h k ^ m = 1 ∧
      ∀ k, ∀ q ∈ H.sub I ^ m, w k * q ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZColumns».«exists_partition» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_exists_partition_c437fe6b702e
