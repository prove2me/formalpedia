-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_of_inv_1108d97397dd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_of_inv_1108d97397dd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:02:29.258081+00:00
-- url     : https://prove2.me/theorems/86dc8d02-13c1-40c2-93f3-d75d5d5b6647
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns smul mem twist of inv 1108d97397dd: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns smul mem twist of inv 1108d97397dd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns smul mem twist of inv 1108d97397dd construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns smul mem twist of inv 1108d97397dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L56-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L56-L78

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
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_of_inv_1108d97397dd {G : SubSystem S x E} {H : SubSystem S x Ω} {I : Chart x} {m c : ℕ}
    {w : Ω} (hw : ∀ q ∈ H.sub I ^ m, w * q ∈ chartRing S x I) {z : E}
    (hz : z ∈ (G.twist (H.pow (c + m))).sub I) : w • z ∈ (G.twist (H.pow c)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZColumns».«smul_mem_twist_of_inv» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_of_inv_1108d97397dd
