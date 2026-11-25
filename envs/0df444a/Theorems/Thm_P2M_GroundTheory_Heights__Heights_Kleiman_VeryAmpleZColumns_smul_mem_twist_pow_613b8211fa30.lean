-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_pow_613b8211fa30
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_pow_613b8211fa30
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:21.349542+00:00
-- url     : https://prove2.me/theorems/828bd8cf-bb7a-5eba-a950-68863cda9526
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns smul mem twist pow 613b8211fa30: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns smul mem twist pow 613b8211fa30
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns smul mem twist pow 613b8211fa30 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns smul mem twist pow 613b8211fa30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L35-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L35-L52

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_pow_613b8211fa30 {G : SubSystem S x E} {H : SubSystem S x Ω} {I : Chart x} {n c : ℕ}
    {q : Ω} (hq : q ∈ H.sub I ^ c) {z : E} (hz : z ∈ (G.twist (H.pow n)).sub I) :
    q • z ∈ (G.twist (H.pow (n + c))).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZColumns».«smul_mem_twist_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_pow_613b8211fa30
